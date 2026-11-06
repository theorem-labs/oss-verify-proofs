(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "nat"; "list"; "true"; "bool"; "cons"; "fst"; "nil"; "app"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "sprop"; "sprop_eqb"; "SVar"; "ss_next"; "SPUle"; "SLit"; "SPUlt"; "holds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA"; "am_eqb"; "am_subst"; "nd_below"; "AHead"; "AK0"; "ANone"; "AV0"; "NDA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "ndX0"; "ndXE"; "AK1"; "bdA"; "bdX"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "tblL"; "A1"; "ldef"; "s_body"; "s_loop"; "X_bodyNc"; "X_latchA"; "frL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "efnode"; "bud_le2"; "phiK"; "fnode"; "efdrop"; "ejcertAF"; "enodeIAF"; "nodeIAF"; "JAF"; "phi_reads"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "add"; "mul"; "div"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vLEN"; "Pre_lo"; "vCFGp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro_eqs"; "z0"; "nd_r2"; "bd_pro"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "K_after0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pf"; "bd0c"; "bd_proL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "KU"; "batom"; "bd_below"; "BI"; "bxK"; "bxN"; "bxS"; "bxV"; "ASv"; "bd_subst"; "bsumK"; "bsumV"; "bd_nn"; "bd_wpos"; "bud_pay"; "mkBX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_certB"; "PhisB"; "cutsBg"; "cutsB"; "FUEL_B"; "HBg"; "cps_B"; "exitsB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch"; "X_bodyN"; "xLC"; "X_latchE"; "pI"; "HNEXT"; "K_body"; "K_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_certA"; "PhisA"; "cutsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1"; "nd_s0"; "cE"; "kE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exitsR"; "ldefR"; "K_after0R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land"; "E_blr0"; "E_blr"; "K0a"; "K0b"; "K1a"; "K1b"; "tv_site"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "X_dp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopEf";
"ndXEf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface"; "al48_cells"; "memcpy48_contractA"; "memcpy48_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface"; "memcpyR_contractA"; "memcpyR_contractA_ex"; "white_hv"; "white_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "K_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_eqs"; "nd_d0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pf.IF"; "P_err"; "P_ok"; "nd_lo0"; "nd_lo_err"; "nd_lo_ok"; "lo_classes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA"; "hideN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "CK0"; "CV0"; "CK_DIV"; "CV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_chk"; "ENDOW"; "bdLand_a1"; "bdLand_b1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_chk2"; "bdLand_a0"; "bdLand_b0"; "bd_bli"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ou.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_exitsR Lib_load_obj_loopE Lib_load_obj_loopEf Lib_load_obj_armkit2 Lib_load_obj_certA Lib_load_obj_certB Lib_load_obj_certB0 Lib_load_obj_certB1 Lib_load_obj_certB2 Lib_load_obj_certB3 Lib_load_obj_certB4 Lib_load_obj_certB5 Lib_load_obj_certB6 Lib_load_obj_certB7 Lib_load_obj_land Lib_load_obj_land_chk Lib_load_obj_land_chk2 Lib_load_obj_pro_eqs Lib_load_obj_epiD1 Lib_load_obj_epiD_eqs Lib_load_obj_epiS1 Lib_load_obj_boxkit Lib_load_obj_certE Lib_load_obj_lglue2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_af_pf Lib_load_obj_ago_pf Lib_load_obj_al_pf Lib_load_obj_aml_pf Lib_load_obj_ap_pf Lib_load_obj_as_pf Lib_load_obj_aus_pf Lib_load_obj_avn_pf Lib_load_obj_avt_pf Lib_load_obj_hv_pf6 Lib_load_obj_pro_pf Lib_load_obj_land_pf Lib_load_obj_certE_pf Lib_load_obj_epi_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module IF. Include Lib_load_obj_iface. End IF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_ifaceL.
Module IFL. Include Lib_load_obj_ifaceL. End IFL.
Module EP. Include Lib_load_obj_epi_pf. End EP.
Module CE. Include Lib_load_obj_certE_pf. End CE.
Module LP. Include Lib_load_obj_land_pf. End LP.
Module PP. Include Lib_load_obj_pro_pf. End PP.

Definition bd_proL : list bitem := ltac2:(tb__ "0|5|
S9S67S6bZ1M0Z0M1S9S4S1S69A2M2S3S1S69Sb2S70S56A1M3A4SbG2A1M4A3S4fS4fSb0Z40A2S8dA2A4S9S67S6bG1G0S9G2S3S1S69S53S68Sb1A2G3A4G4A3S4fS4fS52S68SafA2S68A2S8eA2A4SbS67A1A3A3").
Definition bd0c : list bitem := ltac2:(tb__ "0|5|
S9S67S6bZ1M0Z0M1S9S4S1S69A2M2S3S1S69S3cS70S56A1M3A4SbG2A1M4A3S4fS4fS4fS4fSb0Z40A2S8dA2Z260A2S2aA2A4S9S67S6bG1G0S9G2S3S1S69S32G3A4G4A3S4fS4fS4fS4fS52S68SafA2S68A2S8eA2S52Z20000Z36A2A2S28A2A4SbS67A1A3A3").

Lemma s5_checks_bud : ltac2:(tb__ "0|8|
S1bS1aS8S76S10S1fS92A1M0A1S16Z0M1A1G1S65ScS67SbdScS67S64Sb8A3M2A3A5S7A3S1bS1aS8S6aS14G0A1M3S65A2S7A3S1bS1aS8S6aG3G2A2S7A3S1bS1aS8S6aS14S1fS96A1M4A1S64A2S7A3S1bS1aS8S45S10G4A1SbaS64A3S7A3S1bS1aS8S6aS14S1fS95A1M5A1S64A2S7A3S1bS1aS8S45S10G5A1Sb9S64A3S7A3S1bS1aS8S6aS14S1fS94A1M6A1S64A2S7A3S1bS1aS8S45S10G6A1SbcS64A3S7A3S1bS1aS8S6aS14S1fS93A1M7A1S64A2S7A3S1aS8S45S10G7A1SbbS64A3S7A3A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma s5_checks_loop : ltac2:(tb__ "0|2|
S1bS1aS8S26S84S2dA2S7A3S1bS1aS8S45S10S1fS40A1A1S71S3eS33S3cA1M0A2G0A3S7A3S1bS1aS8S24S25S3eS27S87S7A2M1A2G1A2S7A3S1bS1aS8S26S84S30A2S7A3S1bS1aS8S45S10S1fS41A1A1S71S3fG0A2S34Z0A1A3S7A3S1aS8S24S25S3fG1A2G1A2S7A3A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma bd_proL_sums : ltac2:(tb__ "0|0|
SeS1bS1aS8S75S65A1S7A3S1bS74S65R1A2S1bS1aS1S51S73S65R1A2S8dA2S73S5bR1A2A3S1aS1S51S72S65R1A2S8eA2S72S5bR1A2A3A2A2A2Frho;").
Proof.
  intros rho. pose proof (uval_range rho vLEN) as RL. unfold bd_proL, bd_pro. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [bi_f bi_c lfval aval].
  unfold CV, CV0, cE, kE, CK0, CK_DIV, KU in *. split; [reflexivity|]. split; [|split; lia].
  unfold bd_nn. repeat constructor; unfold bival; cbn [bi_f bi_c lfval aval]; lia.
Qed.

Lemma meas_facts : ltac2:(tb__ "0|1|
S1eSeS1aS8S62S11S12S17S83S81A2A1S10S1fR2A1A1A3S7A3S1aS8S62S11S12S15S81S56A2A1S10S1fR3A1A1A3S7A3S1aS8S62S11S12S15S56S16Z4000000A1A2A1S10S1fR4A1A1A3S7A3S36S11S18R4A1S10S1fR5A1A1A3S1bS50S66R5S83A2S66R5S81A2M0A2S4eG0S54Z2Z1aA2A2A2F_;F_;F_;F_;Frho;FA;").
Proof.
  intros A rho C1 C2 C3 HF.
  pose proof (proj1 (Forall_forall _ _) HF _ (existsb_sprop_eqb _ _ C1)) as H1. rewrite h_ult in H1.
  pose proof (proj1 (Forall_forall _ _) HF _ (existsb_sprop_eqb _ _ C2)) as H2. rewrite h_ule in H2.
  pose proof (proj1 (Forall_forall _ _) HF _ (existsb_sprop_eqb _ _ C3)) as H3. rewrite h_ule, uval_lit in H3 by lia.
  change (2 ^ 26) with 67108864. lia.
Qed.
Lemma s5_checks_meas : ltac2:(tb__ "0|5|
S1bS1aS8S62S11S12S17S83S81A2A1M0S10S1fS80A1A1M1A3S7A3S1bS1aS8S62S11S12S15S81S56A2A1M2G1A3S7A3S1bS1aS8S62S11S12S15S56S16Z4000000A1A2A1M3G1A3S7A3S1bS1aS8S62S11G0S10S1fS9aA1A1M4A3S7A3S1bS1aS8S62S11G2G4A3S7A3S1aS8S62S11G3G4A3S7A3A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma PhisA_reads : ltac2:(tb__ "0|3|
S36S4S6S2A1M0SeOF_;M1A2M2G2S4dSaG0G1R1A3SdG0G1R1A3A2Lp;S8aA3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma SPfamETA_mono : ltac2:(tb__ "0|0|
S6S9cA1S1S1S39S4eR3R2A2S98S0R5R4R2A4S98S0R6R4R3A4F_;F_;Fw;Fb';Fb;Fnodes;").
Proof. intros nodes b b' w Hb (n & rho & tp & Hin & HS & Hm). exists n, rho, tp. split; [exact Hin|]. split; [exact HS | lia]. Qed.

Lemma s5_checks_after : ltac2:(tb__ "0|0|
S1aS8S63S11S11S62S11S12R1A1S10S1fS90A1A1A3Lf;S10S1fS5cA1A1A3S7A3").
Proof. vmc1. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sc0SeS6S20Q40A1A1Sb4OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S60S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S1S9eVCST;R1A2S1bS4eZ0R2A2S50R2Sb3A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S1S9eVXGL;R1A2S1bS4eZ0R2A2S50R2Sb3A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S1Sb7R1A1S9eVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S6S4S4S1S1A2S1A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HCFG : ltac2:(tb__ "0|0|
SbfVFF;S66Vrho0;S58A2Z90A3").
Hypothesis HCEN : ltac2:(tb__ "0|1|
S1S61S1R1SadA3S1aS5S89R2S35S4S4S1S1A2M0S1A2G0SaG0S1A2VFF;A4A2U0A3F_;Fc;").
Let P0 : ltac2:(tb__ "0|0|
SeOFr;") := ltac2:(tb__ "0|0|
SbeVCST;VFB;VFF;A3").

Let BXL : bxt := ltac2:(tb__ "0|0|
S77S3S1S1S51S6fVBX;A1S8dA2S51S6cVBX;A1S8eA2A4S6eVBX;A1S6dVBX;A1A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S23VAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBX;S22Vnd;Ac").
Let JAvL (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S23VAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBXL;S22Vnd;Ac").
Let JAFvL (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S4cVAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBXL;S22VPhi;Vnd;Ad").

Lemma HBXL : BXok_d 7 BXL.
Proof.
  destruct (BXok_d_pair _ BX HBX) as [V0 K0].
  apply (BXok_d_mono0 7 BX BXL HBX); unfold BXL, bxV, bxK, cE, kE, KU in *; cbn [bx2 bxS bxN fst snd]; [reflexivity | lia | lia | reflexivity].
Qed.
Lemma HC0 : ltac2:(tb__ "0|1|
S1aS5S89Z0S35S4S4S1S1A2M0S1A2G0SaG0S1A2VFF;A4A2U0A3"). Proof. apply HCEN. cbn. tauto. Qed.
Lemma HC1 : ltac2:(tb__ "0|1|
S1aS5S89Z1S35S4S4S1S1A2M0S1A2G0SaG0S1A2VFF;A4A2U0A3"). Proof. apply HCEN. cbn. tauto. Qed.
Lemma HC3 : ltac2:(tb__ "0|1|
S1aS5S89Z3S35S4S4S1S1A2M0S1A2G0SaG0S1A2VFF;A4A2U0A3"). Proof. apply HCEN. cbn. tauto. Qed.
Lemma HC5 : ltac2:(tb__ "0|1|
S1aS5S89Z5S35S4S4S1S1A2M0S1A2G0SaG0S1A2VFF;A4A2U0A3"). Proof. apply HCEN. cbn. tauto. Qed.
Lemma HC6 : ltac2:(tb__ "0|1|
S1aS5S89Z6S35S4S4S1S1A2M0S1A2G0SaG0S1A2VFF;A4A2U0A3"). Proof. apply HCEN. cbn. tauto. Qed.

Lemma box_in : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S39S19S0VJAv;S5aA1S91R3R2R1A6S19S0VJAvL;S2bS97S42S65S29A4A1S91R4R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (BXok_d_pair _ BX HBX) as [V0 K0]. destruct (bd_proL_sums rho) as (Swp & Snn & SV & SK).
  apply (SPA_rebox AInv CST XGL NP Kc rho0 P0 FB FF PTrue BX BXL [blkAR] fr_lo bd_pro bd_proL ANone E_blr0 rho tp w); [| | | |exact Swp| |exact Hw];
    unfold BXL, bxV, bxK, cE, kE, KU in *; cbn [bx2 bxS bxN fst snd]; try lia.
  intros _ _. split; [exact Snn|]. unfold cE, kE, KU in *. lia.
Qed.

Lemma after_box : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S39S19S0VJAvL;S2dA1S5cR3R2R1A6S19S0VJAv;S8cA1S5cR4R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (BXok_d_pair _ BX HBX) as [V0 K0].
  apply (SPA_box_out AInv CST XGL NP Kc rho0 P0 FB FF PTrue BX BXL cE kE tvL frL [LA A1; LAK AK1] bd_rest (AHead pH true) K_after0 rho tp w);
    [| | | | | | | |exact Hw]; unfold BXL, bxV, bxK, cE, kE, KU in *; cbn [bx2 bxS bxN fst snd]; lia.
Qed.
Lemma after_step : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S39S19S0VJAFvL;S3bS2dA2S90R3R2R1A6S1bS8fR4A1S19S0VJAv;S8cA1S5cR4R3R2A6A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblL ndA1 K_after0R rho tp w Hw) as [HS HT].
  pose proof (smatchA_facts segs rho tp K_after0R w (proj1 HS)) as HF.
  pose proof exitsR_checks as (_ & _ & _ & Ceq & Cb & Cr).
  assert (HR : Forall (holds rho) rate2).
  { apply Forall_forall. intros f Hf. apply (proj1 (Forall_forall _ _) HF). apply existsb_sprop_eqb. exact (proj1 (forallb_forall _ _) Cr f Hf). }
  split; [exact (ldefR_intro rho (proj2 HT) HR)|].
  apply after_box. rewrite <- Ceq. apply (SPA_refacts_JA segs (JAvL ndA1) rho K_after0R (ss_facts (ax_S K_after0)) tp w HS Cb).
  intros _ _ _ _. apply Forall_forall. intros f Hf. apply (proj1 (Forall_forall _ _) HF). apply existsb_sprop_eqb.
  exact (proj1 (forallb_forall _ _) s5_checks_after f Hf).
Qed.

Lemma after0_step : ltac2:(tb__ "0|1|
SeS6S20Q40A1A1S39S1bS1aS1S66R3S13P191A1A2Z0M0A3S1aS1S66R3S13P19aA1A2G0A3A2S19S0VJAFvL;S3bS2dA2S5cR4R3R2A6S1bS8fR5A1S19S0VJAv;S8cA1S5cR5R4R3A6A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w [Z1 Z2] Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblL ndA1 K_after0 rho tp w Hw) as [HS HT].
  split; [|exact (after_box rho tp w HS)]. apply (ldefR_intro rho (proj2 HT)).
  pose proof (uval_range rho pNX) as RN.
  constructor; [unfold fact_nv, vNV; rewrite h_ule, Z1; lia|]. constructor; [unfold fact_nt; rewrite h_ule, Z2; lia | constructor].
Qed.

Lemma body_step : ltac2:(tb__ "0|4|
SeS6S20Q40A1A1S39S19S0VJAFvL;S3bS2dA2S80R3R2R1A6S1dSeSeS1bS1bS3aR1A1S1bS4eZ0S43S3S4S4S1eS21A2M0S5A2M1S4S1SfA2M2S3G0S5S3S1eS21S85S2dA4U1A4S3S1SfS2eS2fZ18S59A2A4A4R1A2M3A2S50G3S43S3G1G2S3G0S5S3S1eS21S80S2dA4U0A4S3S1SfS2eS2fZ19S59A2A4A4R5A2A2A2A2S19S0VJAvL;S2dA1S85R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblL ndA1 X_bodyN rho tp w Hw) as [HS HT].
  pose proof s5_checks_loop as (C1 & C2 & C3 & _). pose proof s5_checks_meas as (M1 & M2 & M3 & _).
  destruct (meas_facts X_bodyN rho M1 M2 M3 (smatchA_facts segs rho tp X_bodyN w (proj1 HS))) as [Hi Hc].
  destruct (body_carve AInv CST XGL ALA HCST HXGL Kc HKc FB FF BXL PTrue rho0 (bdA A1) (AHead pH true) rho tp w C1 C2 C3 HT HS) as (rho2 & HB & HS2 & EC & EI).
  exists rho2. split; [split; [exact HB|] | exact HS2].
  exact (meas_same rho rho2 25 24 X_bodyN K_body ndA1 ndA1 0%nat 1%nat EI EC Hi Hc ltac:(lia) ltac:(lia)).
Qed.
Lemma latch_step : ltac2:(tb__ "0|4|
SeS6S20Q40A1A1S39S19S0VJAFvL;S3aS30A2S7fR3R2R1A6S1dSeSeS1bS1bS3bR1A1S1bS4eZ0S43S3S4S4S1eS21A2M0S5A2M1S4S1SfA2M2S3G0S5S3S1eS21S86S2dA4U0A4S3S1SfS2eS2fZ1aS59A2A4A4R1A2M3A2S50G3S43S3G1G2S3G0S5S3S1eS21S7fS30A4U1A4S3S1SfS2eS2fZ1S59A2A4A4R5A2A2A2A2S19S0VJAvL;S2dA1S86R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblB ndX0 X_latch rho tp w Hw) as [HS HB].
  pose proof s5_checks_loop as (_ & _ & _ & C1 & C2 & C3).
  destruct (latch_absorb2 AInv CST XGL ALA HCST HXGL Kc HKc FB FF BXL PTrue rho0 (bdX 0) (bdA A1) (AHead pH true) rho tp w C1 C2 C3 HB HS)
    as (rho2 & HT & HS2 & EC & EI & Hi & Hc).
  exists rho2. split; [split; [exact HT|] | exact HS2].
  exact (meas_latch rho rho2 1 26 X_latch K_loop ndX0 ndA1 1%nat 0%nat EI EC Hi Hc ltac:(lia) ltac:(lia)).
Qed.
Lemma dp_step : ltac2:(tb__ "0|6|
SeS6S20Q40A1A1S39S19S0VJAFvL;S3aS2dA2S9aR3R2R1A6S1dS1eS1eS1bS1bS61S4S4S4S1eS21A2M0S5A2M1S4S1SfA2M2A2S3G1G2S3G0S5S3S1eS21R1S2dA4U1M3A4S3S1SfS2eS2fZ14S59A2A4A4M4S7aA3S1bS3aR5A1S1bS4eZ0S43G4R5A2M5A2S50G5S43S3G1G2S3G0S5S3S1eS21S9aS2dA4G3A4S3S1SfS2eS2fZ15S59A2A4A4R5A2A2A2A2A2S19S0VJAvL;S2dA1R1R5R4R3A6A2LT;A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblB ndA1 X_dp rho tp w Hw) as [HS HB].
  pose proof s5_checks_meas as (_ & _ & _ & M1 & M2 & M3).
  destruct (meas_facts X_dp rho M1 M2 M3 (smatchA_facts segs rho tp X_dp w (proj1 HS))) as [Hi Hc].
  assert (HM : forall T, 0 <= efmeasA (T, ndA1, 1%nat, (RL, VLA 20 z0)) rho < efmeasA (X_dp, ndA1, 1%nat, (RL, VLA 21 z0)) rho).
  { intros T. exact (meas_same rho rho 21 20 X_dp T ndA1 ndA1 1%nat 1%nat eq_refl eq_refl Hi Hc ltac:(lia) ltac:(lia)). }
  destruct (dp_split AInv CST XGL Kc FB FF BXL PTrue rho0 ndA1 rho tp w HS) as [(t & Ht & HS2)|HS2].
  - exists (K_dpt t). split; [split; [|split; [exact HB | exact (HM _)]] | exact HS2].
    unfold cutsB. apply in_or_app. left. apply (in_map (fun A => (A, ndA1, 1%nat, (RL, VLA 20 z0))) dp_cuts (K_dpt t)).
    unfold dp_cuts. apply in_or_app. left. apply in_map. exact Ht.
  - exists K_dpB. split; [split; [|split; [exact HB | exact (HM _)]] | exact HS2].
    unfold cutsB. apply in_or_app. left. apply (in_map (fun A => (A, ndA1, 1%nat, (RL, VLA 20 z0))) dp_cuts K_dpB).
    unfold dp_cuts. apply in_or_app. right. left. reflexivity.
Qed.

Lemma HBS : ltac2:(tb__ "0|0|
S4eS6eVBXL;A1S6eVBX;A1A2"). Proof. unfold BXL. cbn [bxS]. lia. Qed.
Lemma HBN : ltac2:(tb__ "0|0|
S4eS6dVBXL;A1S6dVBX;A1A2"). Proof. unfold BXL. cbn [bxN]. lia. Qed.
Lemma HBV : ltac2:(tb__ "0|0|
S4eS6fVBX;A1S6fVBXL;A1A2"). Proof. unfold BXL, bxV, cE. cbn [bx2 fst]. lia. Qed.
Lemma HBK : ltac2:(tb__ "0|0|
S4eS51S6cVBX;A1S52Z14S68A2A2S6cVBXL;A1A2"). Proof. unfold BXL, bxK, kE, KU. cbn [bx2 snd]. lia. Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S2cS0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S5eS0S5dVAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S1S61S1R1S9S1Z0S9S1Zf5S9S1Zf8SbS1A1A3A3A3A3Sb5S0S5dVAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48 : ltac2:(tb__ "0|0|
Sa0S0S5dVAInv;VCST;VXGL;S9fA6").
Hypothesis MCROM : ltac2:(tb__ "0|0|
Sa2S0S5dVAInv;VCST;VXGL;Sa4ZcA7").
Hypothesis MCROML : ltac2:(tb__ "0|0|
Sa2S0S5dVAInv;VCST;VXGL;Sa5ZcA7").
Variable Q : assn.
Hypothesis XPK_T : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S38S0Vok;S19S0VJAv;SacA1Sa9R2R1A5VQ;A4Ftp;Frho;").
Hypothesis XPE_T : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S38S0Vok;S19S0VJAv;SabA1Sa8R2R1A5VQ;A4Ftp;Frho;").

Lemma KDISP_T : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S3dR2A1S38S0Vok;S19S0VJAv;Sa7A1Sa6R3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HL.
  exact (EP.epiDE_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC MC48 (fun _ => Q)
           (fun rho tp _ => XPK_T rho tp) (fun rho tp _ => XPE_T rho tp) rho tp [] HL).
Qed.
Lemma AFTER_T : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S8fR2A1S38S0Vok;S19S0VJAv;S8cA1S5cR3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HL.
  exact (EP.epi_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC MC48 MCROML (fun _ => Q)
           (fun rho tp _ => XPK_T rho tp) (fun rho tp _ => XPE_T rho tp) rho tp [] HL).
Qed.

Let QA : assn := ltac2:(tb__ "0|0|
S39S1cS99S0S35S47S9dS4bVAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBXL;S22S8aAcS35S44S47S48S8bA4A4R1A3VQ;R1A1A2Lw;").
Section GrpT.
Variable gB : nat.
Hypothesis HcertB : ltac2:(tb__ "0|1|
S1aS8S49S0S55S78S7bS7dS55S35S44S44SaeS7cVgB;A1A1M0S79VgB;A1A4S35S44S44G0S7eA4A8S7A3").
Let QB : assn := ltac2:(tb__ "0|0|
S39S1cS99S0S35S47S9dS4bVAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBXL;S22S78AcS35S44S47S48S79VgB;A1A4A4R1A3VQA;R1A1A2Lw;").

Lemma XLa_T : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S38S0Vok;S19S0VJAFvL;S3aS30A2S7fR2R1A5VQA;A4Ftp;Frho;").
Proof.
  intros rho tp. eapply triple_conseq; [intros w Hw; exact (latch_step rho tp w Hw) | intros w Hw; exact Hw |].
  apply triple_ex. intros rho2. apply triple_pure. intros [HT _].
  exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue PhisA ok (map efdrop cutsA) K_loop ndA1 0%nat Q rho2 tp ltac:(left; reflexivity) HT).
Qed.
Lemma XL_T : ltac2:(tb__ "0|1|
SeS6S20Q40A1A1M0G0S38S0Vok;S19S0VJAFvL;S3aS30A2S7fR3R2A5VQB;A4Ftp0;Ftp;Frho;").
Proof. intros rho tp _. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLa_T rho tp)]. Qed.

Lemma XLE2_T : ltac2:(tb__ "0|1|
SeS6S20Q40A1A1M0G0S38S0Vok;S19S0VJAFvL;S3aS31A2S88R3R2A5VQB;A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp _. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errL2_T AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 ok Hok Q KDISP_T rho tp).
Qed.
Lemma XLE2f_T : ltac2:(tb__ "0|1|
SeS6S20Q40A1A1M0G0S38S0Vok;S19S0VJAFvL;S3aS9bA2S88R3R2A5VQB;A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp _. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errLf_T AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBS HBN HBV HBK rho0 ok Hok Q KDISP_T rho tp).
Qed.
Lemma XLE1_T : ltac2:(tb__ "0|1|
SeS6S20Q40A1A1M0G0S38S0Vok;S19S0VJAFvL;S3aS31A2S82R3R2A5VQB;A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp _. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errL1_T AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 ok Hok Q KDISP_T rho tp).
Qed.

Lemma Bg_T : ltac2:(tb__ "0|3|
S1eS21S5S4S1SfA2M0SeS6S20Q40A1A1S61S4S4S4S1eS21A2M1S5A2M2G0A2S3G2G0S3G1S5S3S1eS21R6R5A4R4A4R3A4S79VgB;A1A3S46S78R5R3A3S38S0Vok;S19S0VJAvL;R7A1R8R4R3A5VQA;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisB k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisB PhisA_reads (HBg gB) FUEL_B cps_B NP (cutsBg gB) exitsB ok QA Hok
           HcertB); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn [efdrop fst] in E. injection E as <- <- <-.
  unfold exitsB, h_exits, us_exits in HinX. cbn [map app In] in HinX.
  destruct HinX as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <- <- <-.
  - exact (Lib_load_obj_avn_pf.arm_vn_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC0 ok Hok AC (fun _ => QB) XL_T XLE1_T rho1 tp1 []).
  - exact (Lib_load_obj_avt_pf.arm_vt_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 ok Hok AC (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (Lib_load_obj_af_pf.arm_f_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC3 HC6 ok Hok AC SSC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_pf.handle_f_ok (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (Lib_load_obj_al_pf.arm_l_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 ok Hok AC (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (Lib_load_obj_ap_pf.arm_p_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC0 ok Hok AC (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (Lib_load_obj_aml_pf.arm_ml_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 HCFG ok Hok AC (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (Lib_load_obj_ago_pf.arm_go_T AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BXL HBXL rho0 ok Hok AC (fun _ => QB) XL_T XLE2f_T rho1 tp1 []).
  - exact (Lib_load_obj_as_pf.arm_s_T AInv CST XGL ALA Kc HKc FB FF BXL rho0 ok Hok (fun _ => QB) XL_T rho1 tp1 []).
  - exact (Lib_load_obj_aus_pf.arm_us_T AInv CST XGL ALA Kc HKc FB FF BXL rho0 ok Hok (fun _ => QB) XL_T rho1 tp1 []).
  - exact (Lib_load_obj_aus_pf.arm_us0_T AInv CST XGL ALA Kc HKc FB FF BXL rho0 ok Hok (fun _ => QB) XL_T rho1 tp1 []).
  - exact (Lib_load_obj_hv_pf6.arm_v_T AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BXL HBXL rho0 ok Hok AC MCROM (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (XL_T rho1 tp1 []).
Qed.

End GrpT.
Lemma B_T : ltac2:(tb__ "0|3|
S1eS21S5S4S1SfA2M0SeS6S20Q40A1A1S61S4S4S4S1eS21A2M1S5A2M2G0A2S3G2G0S3G1S5S3S1eS21R6R5A4R4A4R3A4S7aA3S46S78R5R3A3S38S0Vok;S19S0VJAvL;R7A1R8R4R3A5VQA;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi. destruct (cutsB_groups _ Hin) as (g & Hg & Hing).
  assert (Hc : (g = 0 \/ g = 1 \/ g = 2 \/ g = 3 \/ g = 4 \/ g = 5 \/ g = 6 \/ g = 7)%nat) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
  - exact (Bg_T 0%nat Lib_load_obj_certB0.ecertB_ok_0 T nd k rv rho tp Hing Hphi).
  - exact (Bg_T 1%nat Lib_load_obj_certB1.ecertB_ok_1 T nd k rv rho tp Hing Hphi).
  - exact (Bg_T 2%nat Lib_load_obj_certB2.ecertB_ok_2 T nd k rv rho tp Hing Hphi).
  - exact (Bg_T 3%nat Lib_load_obj_certB3.ecertB_ok_3 T nd k rv rho tp Hing Hphi).
  - exact (Bg_T 4%nat Lib_load_obj_certB4.ecertB_ok_4 T nd k rv rho tp Hing Hphi).
  - exact (Bg_T 5%nat Lib_load_obj_certB5.ecertB_ok_5 T nd k rv rho tp Hing Hphi).
  - exact (Bg_T 6%nat Lib_load_obj_certB6.ecertB_ok_6 T nd k rv rho tp Hing Hphi).
  - exact (Bg_T 7%nat Lib_load_obj_certB7.ecertB_ok_7 T nd k rv rho tp Hing Hphi).
Qed.

Lemma A_T : ltac2:(tb__ "0|3|
S1eS21S5S4S1SfA2M0SeS6S20Q40A1A1S61S4S4S4S1eS21A2M1S5A2M2G0A2S3G2G0S3G1S5S3S1eS21R6R5A4R4A4R3A4S8bA3S46S8aR5R3A3S38S0Vok;S19S0VJAvL;R7A1R8R4R3A5VQ;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisA k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisA PhisA_reads H_ecertA_ok FUEL_A cps_loop NP cutsA exitsA ok Q Hok
           ecertA_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn [efdrop fst] in E. injection E as <- <- <-.
  unfold exitsA in HinX. cbn [In] in HinX.
  destruct HinX as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <- <- <-.
  -
    eapply triple_conseq; [intros w Hw; exact (body_step rho1 tp1 w Hw) | intros w Hw; exact Hw |].
    apply triple_ex. intros rho2. apply triple_pure. intros [HB _].
    exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue PhisA ok (map efdrop cutsA) K_body ndA1 1%nat Q rho2 tp1 ltac:(right; left; reflexivity) HB).
  -
    eapply triple_conseq; [intros w Hw; exact (after_step rho1 tp1 w Hw) | intros w Hw; right; exact Hw |].
    apply triple_pure. intros HL. exact (AFTER_T rho1 tp1 HL).
  -
    eapply triple_conseq; [intros w Hw; exact (dp_step rho1 tp1 w Hw) | intros w Hw; exact Hw |].
    apply triple_ex. intros T'. apply triple_pure. intros (HinB & HB & _).
    exact (B_T T' ndA1 1%nat (RL, VLA 20 z0) rho1 tp1 HinB HB).
  - exact (XLa_T rho1 tp1).
  -
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    exact (CE.err7_T AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 ok Hok Q KDISP_T rho1 tp1).
Qed.

Lemma TGT_bodyN_T : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S3bR2A1S38S0Vok;S19S0VJAFvL;S3bS2dA2S80R3R2A5VQ;A4F_;Ftp;Frho2;").
Proof.
  intros rho2 tp _. eapply triple_conseq; [intros w Hw; exact (body_step rho2 tp w Hw) | intros w Hw; exact Hw |].
  apply triple_ex. intros rho3. apply triple_pure. intros [HB _].
  exact (A_T K_body ndA1 1%nat (RL, VLA 24 z0) rho3 tp ltac:(right; left; reflexivity) HB).
Qed.
Lemma TGT_after0_T : ltac2:(tb__ "0|1|
SeS6S20Q40A1A1S3bR2A1S1bS1aS1S66R3S13P191A1A2Z0M0A3S1aS1S66R3S13P19aA1A2G0A3A2S38S0Vok;S19S0VJAFvL;S3bS2dA2S5cR4R3A5VQ;A4F_;F_;Ftp;Frho2;").
Proof.
  intros rho2 tp _ HZ. eapply triple_conseq; [intros w Hw; exact (after0_step rho2 tp w HZ Hw) | intros w Hw; exact Hw |].
  apply triple_pure. intros HL. exact (AFTER_T rho2 tp HL).
Qed.
Lemma CONT_blr_T : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S38S0Vok;S19S0VJAv;S5aA1S91R2R1A5VQ;A4Ftp;Frho;").
Proof.
  intros rho tp. pose proof s5_checks_bud as (Cpay & Cbp & Cbr & Cb1 & Cl1 & Cb2 & Cl2 & Cb3 & Cl3 & Cb4 & Cl4).
  eapply triple_conseq; [intros w Hw; exact (box_in rho tp w Hw) | intros w Hw; exact Hw |].
  exact (LP.blr_land_sound AInv CST XGL ALA HCST HXGL Kc HKc FB FF BXL HBXL PTrue rho0 HXlits (fun _ _ _ H => H) ok Hok AC bd0c Q
           TGT_bodyN_T TGT_after0_T
           (fun rho2 tp2 HL => CE.errB_T AInv CST XGL ALA Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 ok Hok Q KDISP_T rho2 tp2 HL)
           (fun rho2 tp2 HL => CE.errA_T AInv CST XGL ALA Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 ok Hok Q KDISP_T rho2 tp2 HL)
           Cb1 Cl1 Cb2 Cl2 Cb3 Cl3 Cb4 Cl4 Cbr bd_proL rho tp Cbp (payA_of_bud_pay NP rho0 P0 _ _ _ _ _ Cpay)).
Qed.

Theorem lo_body_T : ltac2:(tb__ "0|0|
S6S20Q40A1A1S38S0Vok;S19S0VJAv;SaaA1S57Vrho0;R1A5VQ;A4Ftp0;").
Proof.
  intros tp0.
  exact (PP.pro_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 HC5 ok Hok AC SSC MC48 Q CONT_blr_T XPE_T tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S5fS0S5dVAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S1S61S1R1S9S1Z0S9S1Zf5S9S1Zf8SbS1A1A3A3A3A3Sb6S0S5dVAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48X : ltac2:(tb__ "0|0|
Sa1S0S5dVAInv;VCST;VXGL;S9fA6").
Hypothesis MCROMX : ltac2:(tb__ "0|0|
Sa3S0S5dVAInv;VCST;VXGL;Sa4ZcA7").
Hypothesis MCROMLX : ltac2:(tb__ "0|0|
Sa3S0S5dVAInv;VCST;VXGL;Sa5ZcA7").
Variable Q : world -> Prop.
Hypothesis XPK_E : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S37S0S19S0VJAv;SacA1Sa9R2R1A5VQ;A3Ftp;Frho;").
Hypothesis XPE_E : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S37S0S19S0VJAv;SabA1Sa8R2R1A5VQ;A3Ftp;Frho;").

Lemma KDISP_E : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S3dR2A1S37S0S19S0VJAv;Sa7A1Sa6R3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HL.
  exact (EP.epiDE_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX MC48X (fun _ _ => Q) (fun _ _ _ _ _ H => H)
           (fun rho tp _ => XPK_E rho tp) (fun rho tp _ => XPE_E rho tp) rho tp [] HL).
Qed.
Lemma AFTER_E : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S8fR2A1S37S0S19S0VJAv;S8cA1S5cR3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HL.
  exact (EP.epi_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX MC48X MCROMLX (fun _ _ => Q) (fun _ _ _ _ _ H => H)
           (fun rho tp _ => XPK_E rho tp) (fun rho tp _ => XPE_E rho tp) rho tp [] HL).
Qed.

Let QAe (b : Z) : world -> Prop := ltac2:(tb__ "0|0|
S39S1cS98S0S35S44S9cS4aVAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBXL;S22S8aAcS8bA4Vb;R1A4VQ;R1A1A2Lw;").
Section GrpE.
Variable gB : nat.
Hypothesis HcertB : ltac2:(tb__ "0|1|
S1aS8S49S0S55S78S7bS7dS55S35S44S44SaeS7cVgB;A1A1M0S79VgB;A1A4S35S44S44G0S7eA4A8S7A3").
Let QBe (b : Z) : world -> Prop := ltac2:(tb__ "0|0|
S39S1cS98S0S35S44S9cS4aVAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBXL;S22S78AcS79VgB;A1A4Vb;R1A4VQAe;Vb;R1A2A2Lw;").
Let FAMB : Z -> list word -> assn := fun b _ => QBe b.
Lemma QAe_mono : ltac2:(tb__ "0|0|
S1S1S39S4eR3R2A2VQAe;R4R2A2VQAe;R4R3A2F_;F_;Fw;Fb';Fb;").
Proof. intros b b' w Hb [H|H]; [left; exact (SPfamETA_mono _ b b' w Hb H) | right; exact H]. Qed.
Lemma FAMB_mono : ltac2:(tb__ "0|0|
S1S1S6S20Q40A1A1S39S4eR4R3A2VFAMB;R5R3R2A3VFAMB;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Proof. intros b b' tp0 w Hb [H|H]; [left; exact (SPfamETA_mono _ b b' w Hb H) | right; exact (QAe_mono b b' w Hb H)]. Qed.

Lemma XLa_E : ltac2:(tb__ "0|1|
SeS6S20Q40A1A1S37S0S19S0VJAFvL;S3aS30A2S7fR2R1A5VQAe;S43S3S4S4S1eS21A2M0S5A2S4S1SfA2S3G0S5S3S1eS21S7fS30A4U1A4S3S1SfS2eS2fZ1S59A2A4A4R2A2A1A3Ftp;Frho;").
Proof.
  intros rho tp. eapply etriple_conseq; [intros w Hw; exact (latch_step rho tp w Hw) | intros w Hw; exact Hw |].
  apply etriple_ex. intros rho2. apply etriple_pure. intros [HT HM].
  exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue PhisA cutsA K_loop ndA1 0%nat (RL, VLA 26 z0) Q _ rho2 tp ltac:(left; reflexivity) HT HM).
Qed.
Lemma XL_E : ltac2:(tb__ "0|2|
SeS6S20Q40A1A1M0G0S37S0S19S0VJAFvL;S3aS30A2S7fR3R2A5VFAMB;S43S3S4S4S1eS21A2M1S5A2S4S1SfA2S3G1S5S3S1eS21S7fS30A4U1A4S3S1SfS2eS2fZ1S59A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLa_E rho tp)]. Qed.
Lemma XLE2_E : ltac2:(tb__ "0|2|
SeS6S20Q40A1A1M0G0S37S0S19S0VJAFvL;S3aS31A2S88R3R2A5VFAMB;S43S3S4S4S1eS21A2M1S5A2S4S1SfA2S3G1S5S3S1eS21S88S31A4U1A4S3S1SfS2eS2fZ1S59A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errL2_E AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 Q KDISP_E rho tp).
Qed.
Lemma XLE2f_E : ltac2:(tb__ "0|2|
SeS6S20Q40A1A1M0G0S37S0S19S0VJAFvL;S3aS9bA2S88R3R2A5VFAMB;S43S3S4S4S1eS21A2M1S5A2S4S1SfA2S3G1S5S3S1eS21S88S9bA4U1A4S3S1SfS2eS2fZ1S59A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errLf_E AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBS HBN HBV HBK rho0 Q KDISP_E rho tp).
Qed.
Lemma XLE1_E : ltac2:(tb__ "0|2|
SeS6S20Q40A1A1M0G0S37S0S19S0VJAFvL;S3aS31A2S82R3R2A5VFAMB;S43S3S4S4S1eS21A2M1S5A2S4S1SfA2S3G1S5S3S1eS21S82S31A4U1A4S3S1SfS2eS2fZ1S59A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errL1_E AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 Q KDISP_E rho tp).
Qed.

Lemma Bg_E : ltac2:(tb__ "0|3|
S1eS21S5S4S1SfA2M0SeS6S20Q40A1A1S61S4S4S4S1eS21A2M1S5A2M2G0A2S3G2G0S3G1S5S3S1eS21R6R5A4R4A4R3A4S79VgB;A1A3S46S78R5R3A3S37S0S19S0VJAvL;R7A1R8R4R3A5VQAe;S43S3G2G0S3G1S5S3S1eS21R8R7A4R6A4R5A4R4A2A1A3F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisB k) nd T rho tp _ Hphi).
  refine (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisB PhisA_reads (HBg gB) FUEL_B cps_B NP (cutsBg gB) exitsB QAe QAe_mono HcertB _ T nd k rv rho tp Hin).
  intros X ndX kX rvX rho1 tp1 HinX.
  unfold exitsB, h_exits, us_exits in HinX. cbn [map app In] in HinX.
  destruct HinX as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <- <- <-.
  - exact (Lib_load_obj_avn_pf.arm_vn_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC0 ACX FAMB FAMB_mono XL_E XLE1_E rho1 tp1 []).
  - exact (Lib_load_obj_avt_pf.arm_vt_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 ACX FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (Lib_load_obj_af_pf.arm_f_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC3 HC6 ACX SSCX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_pf.handle_f_ok_ex FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (Lib_load_obj_al_pf.arm_l_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 ACX FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (Lib_load_obj_ap_pf.arm_p_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC0 ACX FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (Lib_load_obj_aml_pf.arm_ml_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 HCFG ACX FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (Lib_load_obj_ago_pf.arm_go_E AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BXL HBXL rho0 ACX FAMB FAMB_mono XL_E XLE2f_E rho1 tp1 []).
  - exact (Lib_load_obj_as_pf.arm_s_E AInv CST XGL ALA Kc HKc FB FF BXL rho0 FAMB FAMB_mono XL_E rho1 tp1 []).
  - exact (Lib_load_obj_aus_pf.arm_us_E AInv CST XGL ALA Kc HKc FB FF BXL rho0 FAMB FAMB_mono XL_E rho1 tp1 []).
  - exact (Lib_load_obj_aus_pf.arm_us0_E AInv CST XGL ALA Kc HKc FB FF BXL rho0 FAMB FAMB_mono XL_E rho1 tp1 []).
  - exact (Lib_load_obj_hv_pf6.arm_v_E AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BXL HBXL rho0 ACX MCROMX FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (XL_E rho1 tp1 []).
Qed.

End GrpE.
Lemma B_E : ltac2:(tb__ "0|3|
S1eS21S5S4S1SfA2M0SeS6S20Q40A1A1S61S4S4S4S1eS21A2M1S5A2M2G0A2S3G2G0S3G1S5S3S1eS21R6R5A4R4A4R3A4S7aA3S46S78R5R3A3S37S0S19S0VJAvL;R7A1R8R4R3A5VQAe;S43S3G2G0S3G1S5S3S1eS21R8R7A4R6A4R5A4R4A2A1A3F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi. destruct (cutsB_groups _ Hin) as (g & Hg & Hing).
  assert (Hc : (g = 0 \/ g = 1 \/ g = 2 \/ g = 3 \/ g = 4 \/ g = 5 \/ g = 6 \/ g = 7)%nat) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
  - exact (Bg_E 0%nat Lib_load_obj_certB0.ecertB_ok_0 T nd k rv rho tp Hing Hphi).
  - exact (Bg_E 1%nat Lib_load_obj_certB1.ecertB_ok_1 T nd k rv rho tp Hing Hphi).
  - exact (Bg_E 2%nat Lib_load_obj_certB2.ecertB_ok_2 T nd k rv rho tp Hing Hphi).
  - exact (Bg_E 3%nat Lib_load_obj_certB3.ecertB_ok_3 T nd k rv rho tp Hing Hphi).
  - exact (Bg_E 4%nat Lib_load_obj_certB4.ecertB_ok_4 T nd k rv rho tp Hing Hphi).
  - exact (Bg_E 5%nat Lib_load_obj_certB5.ecertB_ok_5 T nd k rv rho tp Hing Hphi).
  - exact (Bg_E 6%nat Lib_load_obj_certB6.ecertB_ok_6 T nd k rv rho tp Hing Hphi).
  - exact (Bg_E 7%nat Lib_load_obj_certB7.ecertB_ok_7 T nd k rv rho tp Hing Hphi).
Qed.

Lemma A_E : ltac2:(tb__ "0|3|
S1eS21S5S4S1SfA2M0SeS6S20Q40A1A1S61S4S4S4S1eS21A2M1S5A2M2G0A2S3G2G0S3G1S5S3S1eS21R6R5A4R4A4R3A4S8bA3S46S8aR5R3A3S37S0S19S0VJAvL;R7A1R8R4R3A5VQ;A3F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisA k) nd T rho tp _ Hphi).
  refine (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisA PhisA_reads H_ecertA_ok FUEL_A cps_loop NP cutsA exitsA (fun _ w => Q w)
            (fun b b' w _ H => H) ecertA_ok _ T nd k rv rho tp Hin).
  intros X ndX kX rvX rho1 tp1 HinX. unfold exitsA in HinX. cbn [In] in HinX.
  destruct HinX as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <- <- <-.
  - eapply etriple_conseq; [intros w Hw; exact (body_step rho1 tp1 w Hw) | intros w Hw; exact Hw |].
    apply etriple_ex. intros rho2. apply etriple_pure. intros [HB HM].
    exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue PhisA cutsA K_body ndA1 1%nat (RL, VLA 24 z0) Q _ rho2 tp1 ltac:(right; left; reflexivity) HB HM).
  - eapply etriple_conseq; [intros w Hw; exact (after_step rho1 tp1 w Hw) | intros w Hw; right; exact Hw |].
    apply etriple_pure. intros HL. exact (AFTER_E rho1 tp1 HL).
  - eapply etriple_conseq; [intros w Hw; exact (dp_step rho1 tp1 w Hw) | intros w Hw; exact Hw |].
    apply etriple_ex. intros T'. apply etriple_pure. intros (HinB & HB & HM).
    eapply etriple_conseq; [intros w Hw; exact Hw | | exact (B_E T' ndA1 1%nat (RL, VLA 20 z0) rho1 tp1 HinB HB)].
    intros w Hw. exact (QAe_mono _ _ w (Z.lt_le_incl _ _ (proj2 HM)) Hw).
  - exact (XLa_E rho1 tp1).
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    exact (CE.err7_E AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 Q KDISP_E rho1 tp1).
Qed.

Lemma TGT_bodyN_E : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S3bR2A1S37S0S19S0VJAFvL;S3bS2dA2S80R3R2A5VQ;A3F_;Ftp;Frho2;").
Proof.
  intros rho2 tp _. eapply etriple_conseq; [intros w Hw; exact (body_step rho2 tp w Hw) | intros w Hw; exact Hw |].
  apply etriple_ex. intros rho3. apply etriple_pure. intros [HB _].
  exact (A_E K_body ndA1 1%nat (RL, VLA 24 z0) rho3 tp ltac:(right; left; reflexivity) HB).
Qed.
Lemma TGT_after0_E : ltac2:(tb__ "0|1|
SeS6S20Q40A1A1S3bR2A1S1bS1aS1S66R3S13P191A1A2Z0M0A3S1aS1S66R3S13P19aA1A2G0A3A2S37S0S19S0VJAFvL;S3bS2dA2S5cR4R3A5VQ;A3F_;F_;Ftp;Frho2;").
Proof.
  intros rho2 tp _ HZ. eapply etriple_conseq; [intros w Hw; exact (after0_step rho2 tp w HZ Hw) | intros w Hw; exact Hw |].
  apply etriple_pure. intros HL. exact (AFTER_E rho2 tp HL).
Qed.
Lemma CONT_blr_E : ltac2:(tb__ "0|0|
SeS6S20Q40A1A1S37S0S19S0VJAv;S5aA1S91R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. pose proof s5_checks_bud as (Cpay & Cbp & Cbr & Cb1 & Cl1 & Cb2 & Cl2 & Cb3 & Cl3 & Cb4 & Cl4).
  eapply etriple_conseq; [intros w Hw; exact (box_in rho tp w Hw) | intros w Hw; exact Hw |].
  exact (LP.blr_land_complete AInv CST XGL ALA HCST HXGL Kc HKc FB FF BXL HBXL PTrue rho0 HXlits (fun _ _ _ H => H) ACX bd0c Q
           TGT_bodyN_E TGT_after0_E
           (fun rho2 tp2 HL => CE.errB_E AInv CST XGL ALA Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 Q KDISP_E rho2 tp2 HL)
           (fun rho2 tp2 HL => CE.errA_E AInv CST XGL ALA Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 Q KDISP_E rho2 tp2 HL)
           Cb1 Cl1 Cb2 Cl2 Cb3 Cl3 Cb4 Cl4 Cbr bd_proL rho tp Cbp (payA_of_bud_pay NP rho0 P0 _ _ _ _ _ Cpay)).
Qed.

Theorem lo_body_E : ltac2:(tb__ "0|0|
S6S20Q40A1A1S37S0S19S0VJAv;SaaA1S57Vrho0;R1A5VQ;A3Ftp0;").
Proof.
  intros tp0.
  exact (PP.pro_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 HC5 ACX SSCX MC48X (fun _ _ => Q) (fun _ _ _ _ _ H => H)
           (fun rho tp _ => CONT_blr_E rho tp) (fun rho tp _ => XPE_E rho tp) tp0).
Qed.
End Existence.
End Sum.

Theorem load_obj_ok : IFL.load_obj_stmtL.
Proof.
  intros AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC MC48 MCROM MCROML tp0.
  eapply triple_conseq; [intros w Hw; exact (JA_pre_intro segs AInv CST XGL NP Kc (IF.P0_los CST FB FF) FB FF BX PTrue rho0 IF.nd_lo0 Pre_lo tp0 w Hw) | intros w Hw; exact Hw |].
  apply (TRs_pureP segs ok _ (IF.P0_los CST FB FF rho0)).
  { intros w Hw. exact (SPA_JA_P0_get AInv CST XGL NP Kc rho0 (IF.P0_los CST FB FF) FB FF PTrue BX IF.nd_lo0 Pre_lo rho0 tp0 w Hw). }
  intros HP0s. pose proof HP0s as (HP0 & HCFG & HCEN).
  eapply triple_conseq; [intros w Hw; exact (SPA_JA_P0_set AInv CST XGL NP Kc rho0 (IF.P0_los CST FB FF) FB FF PTrue (P0_lo CST FB FF) BX IF.nd_lo0 Pre_lo rho0 tp0 w HP0 Hw) | intros w Hw; exact Hw |].
  apply (lo_body_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 HCFG HCEN ok Hok AC SSC MC48 MCROM MCROML
           (LQPA segs NP rho0 tp0 (IF.Posts_loJ AInv CST XGL Kc FB FF BX))).
  - intros rho tp.
    eapply triple_conseq; [intros w Hw; exact (SPA_JA_P0_set AInv CST XGL NP Kc rho0 (P0_lo CST FB FF) FB FF PTrue (IF.P0_los CST FB FF) BX IF.nd_lo_ok IF.P_ok rho tp w HP0s Hw) | |
      exact (exit_postGA segs AInv CST XGL NP Kc (IF.P0_los CST FB FF) FB FF BX PTrue ok rho0 tp0 IF.nd_lo_ok (IF.Posts_loJ AInv CST XGL Kc FB FF BX) IF.P_ok (fun _ => False)
               ltac:(right; left; reflexivity) rho tp)].
    intros w [[]|Hw]; exact Hw.
  - intros rho tp.
    eapply triple_conseq; [intros w Hw; exact (SPA_JA_P0_set AInv CST XGL NP Kc rho0 (P0_lo CST FB FF) FB FF PTrue (IF.P0_los CST FB FF) BX IF.nd_lo_err IF.P_err rho tp w HP0s Hw) | |
      exact (exit_postGA segs AInv CST XGL NP Kc (IF.P0_los CST FB FF) FB FF BX PTrue ok rho0 tp0 IF.nd_lo_err (IF.Posts_loJ AInv CST XGL Kc FB FF BX) IF.P_err (fun _ => False)
               ltac:(left; reflexivity) rho tp)].
    intros w [[]|Hw]; exact Hw.
Qed.

Theorem load_obj_ok_ex : IFL.load_obj_stmt_exL.
Proof.
  intros AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX MC48X MCROMX MCROMLX tp0.
  eapply etriple_conseq; [intros w Hw; exact (JA_pre_intro segs AInv CST XGL NP Kc (IF.P0_los CST FB FF) FB FF BX PTrue rho0 IF.nd_lo0 Pre_lo tp0 w Hw) | intros w Hw; exact Hw |].
  apply (TRe_pureP segs _ (IF.P0_los CST FB FF rho0)).
  { intros w Hw. exact (SPA_JA_P0_get AInv CST XGL NP Kc rho0 (IF.P0_los CST FB FF) FB FF PTrue BX IF.nd_lo0 Pre_lo rho0 tp0 w Hw). }
  intros HP0s. pose proof HP0s as (HP0 & HCFG & HCEN).
  eapply etriple_conseq; [intros w Hw; exact (SPA_JA_P0_set AInv CST XGL NP Kc rho0 (IF.P0_los CST FB FF) FB FF PTrue (P0_lo CST FB FF) BX IF.nd_lo0 Pre_lo rho0 tp0 w HP0 Hw) | intros w Hw; exact Hw |].
  apply (lo_body_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 HCFG HCEN ACX SSCX MC48X MCROMX MCROMLX
           (LQPA segs NP rho0 tp0 (IF.Posts_loJ AInv CST XGL Kc FB FF BX))).
  - intros rho tp.
    eapply etriple_conseq; [intros w Hw; exact (SPA_JA_P0_set AInv CST XGL NP Kc rho0 (P0_lo CST FB FF) FB FF PTrue (IF.P0_los CST FB FF) BX IF.nd_lo_ok IF.P_ok rho tp w HP0s Hw) | |
      exact (eexit_postGA segs AInv CST XGL NP Kc (IF.P0_los CST FB FF) FB FF BX PTrue rho0 tp0 IF.nd_lo_ok (IF.Posts_loJ AInv CST XGL Kc FB FF BX) IF.P_ok (fun _ => False)
               ltac:(right; left; reflexivity) rho tp)].
    intros w [[]|Hw]; exact Hw.
  - intros rho tp.
    eapply etriple_conseq; [intros w Hw; exact (SPA_JA_P0_set AInv CST XGL NP Kc rho0 (P0_lo CST FB FF) FB FF PTrue (IF.P0_los CST FB FF) BX IF.nd_lo_err IF.P_err rho tp w HP0s Hw) | |
      exact (eexit_postGA segs AInv CST XGL NP Kc (IF.P0_los CST FB FF) FB FF BX PTrue rho0 tp0 IF.nd_lo_err (IF.Posts_loJ AInv CST XGL Kc FB FF BX) IF.P_err (fun _ => False)
               ltac:(left; reflexivity) rho tp)].
    intros w [[]|Hw]; exact Hw.
Qed.
