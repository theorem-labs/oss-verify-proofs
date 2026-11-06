(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "nat"; "true"; "bool"; "cons"; "fst"; "nil"; "app"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "sprop"; "sprop_eqb"; "SVar"; "ss_next"; "SPUle"; "SLit"; "SPUlt"; "holds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA"; "am_eqb"; "am_subst"; "nd_below"; "AHead"; "AK0"; "ANone"; "AV0"; "NDA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "ndX0"; "ndXE"; "AK1"; "bdA"; "bdX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblB"; "tblL"; "A1"; "ldef"; "s_body"; "s_loop"; "P0_lo"; "X_bodyNc"; "X_latchA"; "frL"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "add"; "mul"; "div"; "pow"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "bud_le2"; "efnode"; "fnode"; "phiK"; "efdrop"; "enodeIAF"; "nodeIAF"; "JAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs"; "z0"; "nd_r2"; "bd_pro"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "K_after0"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pf"; "bd0c"; "bd_proL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "KU"; "batom"; "bd_below"; "BI"; "bxK"; "bxN"; "bxS"; "bxV"; "ASv"; "bd_subst"; "bsumK"; "bsumV"; "bd_nn"; "bd_wpos"; "bud_pay"; "mkBX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "X_bodyN"; "xLC"; "X_latchE"; "pI"; "HNEXT"; "K_body"; "K_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vLEN"; "Pre_lo"; "vCFGp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_certA"; "PhisA"; "cutsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_certB"; "cutsB"; "PhisB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1"; "nd_s0"; "cE"; "kE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "ldefR"; "K_after0R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.Lib_load_obj_land"; "E_blr0"; "E_blr"; "K0a"; "K0b"; "K1a"; "K1b"; "tv_site"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "X_dp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf"; "ndXEf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA";
"jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface"; "al48_cells"; "memcpy48_contractA"; "memcpy48_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface"; "white_hv"; "memcpyR_contractA"; "memcpyR_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "K_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "nd_d0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pf.IF"; "P_err"; "P_ok"; "nd_lo0"; "nd_lo_err"; "nd_lo_ok"; "lo_classes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "CK0"; "CV0"; "CK_DIV"; "CV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_land_chk"; "ENDOW"; "bdLand_a1"; "bdLand_b1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_land_chk2"; "bdLand_a0"; "bdLand_b0"; "bd_bli"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_certB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_certA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_certB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.Lib_load_obj_land OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_land_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_land_chk2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_load_obj_boxkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_certE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_lglue2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ff.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module IF. Include Lib_load_obj_iface. End IF.
Module EP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epi_pf. End EP.
Module CE. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f1.Lib_load_obj_certE_pf. End CE.
Module LP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_land_pf. End LP.
Module PP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_pro_pf. End PP.

Definition bd_proL : list bitem := ltac2:(tb__ "0|5|
S9S5fS63Z1M0Z0M1S9S4S0S61A2M2S3S0S61SaaS68S7dA1M3A4SbG2A1M4A3S43S43Sa8Z40A2S87A2A4S9S5fS63G1G0S9G2S3S0S61S47S60Sa9A2G3A4G4A3S43S43S46S60Sa7A2S60A2S88A2A4SbS5fA1A3A3").
Definition bd0c : list bitem := ltac2:(tb__ "0|5|
S9S5fS63Z1M0Z0M1S9S4S0S61A2M2S3S0S61S3aS68S7dA1M3A4SbG2A1M4A3S43S43S43S43Sa8Z40A2S87A2Z260A2S2aA2A4S9S5fS63G1G0S9G2S3S0S61S32G3A4G4A3S43S43S43S43S46S60Sa7A2S60A2S88A2S46Z20000Z36A2A2S28A2A4SbS5fA1A3A3").

Lemma s5_checks_bud : ltac2:(tb__ "0|8|
S1bS1aS8S6eS10S20S8cA1M0A1S16Z0M1A1G1S5dScS5fSb5ScS5fS5cSb0A3M2A3A5S7A3S1bS1aS8S62S14G0A1M3S5dA2S7A3S1bS1aS8S62G3G2A2S7A3S1bS1aS8S62S14S20S90A1M4A1S5cA2S7A3S1bS1aS8S4cS10G4A1Sb2S5cA3S7A3S1bS1aS8S62S14S20S8fA1M5A1S5cA2S7A3S1bS1aS8S4cS10G5A1Sb1S5cA3S7A3S1bS1aS8S62S14S20S8eA1M6A1S5cA2S7A3S1bS1aS8S4cS10G6A1Sb4S5cA3S7A3S1bS1aS8S62S14S20S8dA1M7A1S5cA2S7A3S1aS8S4cS10G7A1Sb3S5cA3S7A3A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma s5_checks_loop : ltac2:(tb__ "0|2|
S1bS1aS8S26S75S2dA2S7A3S1bS1aS8S4cS10S20S3fA1A1S69S3cS33S3aA1M0A2G0A3S7A3S1bS1aS8S24S25S3cS27S78S7A2M1A2G1A2S7A3S1bS1aS8S26S75S30A2S7A3S1bS1aS8S4cS10S20S40A1A1S69S3dG0A2S34Z0A1A3S7A3S1aS8S24S25S3dG1A2G1A2S7A3A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma bd_proL_sums : ltac2:(tb__ "0|0|
SeS1bS1aS8S6dS5dA1S7A3S1bS6cS5dR1A2S1bS1aS0S45S6bS5dR1A2S87A2S6bS57R1A2A3S1aS0S45S6aS5dR1A2S88A2S6aS57R1A2A3A2A2A2Frho;").
Proof.
  intros rho. pose proof (uval_range rho vLEN) as RL. unfold bd_proL, bd_pro. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [bi_f bi_c lfval aval].
  unfold CV, CV0, cE, kE, CK0, CK_DIV, KU in *. split; [reflexivity|]. split; [|split; lia].
  unfold bd_nn. repeat constructor; unfold bival; cbn [bi_f bi_c lfval aval]; lia.
Qed.

Lemma meas_facts : ltac2:(tb__ "0|1|
S1fSeS1aS8S59S11S12S17S74S72A2A1S10S20R2A1A1A3S7A3S1aS8S59S11S12S15S72S7dA2A1S10S20R3A1A1A3S7A3S1aS8S59S11S12S15S7dS16Z4000000A1A2A1S10S20R4A1A1A3S7A3S4aS11S18R4A1S10S20R5A1A1A3S1bS44S5eR5S74A2S5eR5S72A2M0A2S42G0S48Z2Z1aA2A2A2F_;F_;F_;F_;Frho;FA;").
Proof.
  intros A rho C1 C2 C3 HF.
  pose proof (proj1 (Forall_forall _ _) HF _ (existsb_sprop_eqb _ _ C1)) as H1. rewrite h_ult in H1.
  pose proof (proj1 (Forall_forall _ _) HF _ (existsb_sprop_eqb _ _ C2)) as H2. rewrite h_ule in H2.
  pose proof (proj1 (Forall_forall _ _) HF _ (existsb_sprop_eqb _ _ C3)) as H3. rewrite h_ule, uval_lit in H3 by lia.
  change (2 ^ 26) with 67108864. lia.
Qed.
Lemma s5_checks_meas : ltac2:(tb__ "0|5|
S1bS1aS8S59S11S12S17S74S72A2A1M0S10S20S71A1A1M1A3S7A3S1bS1aS8S59S11S12S15S72S7dA2A1M2G1A3S7A3S1bS1aS8S59S11S12S15S7dS16Z4000000A1A2A1M3G1A3S7A3S1bS1aS8S59S11G0S10S20S94A1A1M4A3S7A3S1bS1aS8S59S11G2G4A3S7A3S1aS8S59S11G3G4A3S7A3A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma PhisA_reads : ltac2:(tb__ "0|3|
S4aS4S5S1A1M0SeOF_;M1A2M2G2S54SaG0G1R1A3SdG0G1R1A3A2Lp;S82A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma SPfamETA_mono : ltac2:(tb__ "0|0|
S5S96A1S0S0S37S42R3R2A2S92S2R5R4R2A4S92S2R6R4R3A4F_;F_;Fw;Fb';Fb;Fnodes;").
Proof. intros nodes b b' w Hb (n & rho & tp & Hin & HS & Hm). exists n, rho, tp. split; [exact Hin|]. split; [exact HS | lia]. Qed.

Lemma s5_checks_after : ltac2:(tb__ "0|0|
S1aS8S5bS11S11S59S11S12R1A1S10S20S8aA1A1A3Lf;S10S20S58A1A1A3S7A3").
Proof. vmc1. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sb7SeS5S1eQ40A1A1SacOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S98VCST;R1A2S1bS42Z0R2A2S44R2SabA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S98VXGL;R1A2S1bS42Z0R2A2S44R2SabA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S0SafR1A1S98VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S5S4S4S0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HCFG : ltac2:(tb__ "0|0|
Sb6VFF;S5eVrho0;S7fA2Z90A3").
Hypothesis HCEN : ltac2:(tb__ "0|1|
S0S5aS0R1Sa6A3S1aS6S81R2S49S4S4S0S0A2M0S0A2G0SaG0S0A2VFF;A4A2U0A3F_;Fc;").
Let P0 : ltac2:(tb__ "0|0|
SeOFr;") := ltac2:(tb__ "0|0|
S3eVCST;VFB;VFF;A3").

Let BXL : bxt := ltac2:(tb__ "0|0|
S6fS3S0S0S45S67VBX;A1S87A2S45S64VBX;A1S88A2A4S66VBX;A1S65VBX;A1A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S23VAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBX;S22Vnd;Ac").
Let JAvL (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S23VAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBXL;S22Vnd;Ac").
Let JAFvL (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S53VAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBXL;S22VPhi;Vnd;Ad").

Lemma HBXL : BXok_d 7 BXL.
Proof.
  destruct (BXok_d_pair _ BX HBX) as [V0 K0].
  apply (BXok_d_mono0 7 BX BXL HBX); unfold BXL, bxV, bxK, cE, kE, KU in *; cbn [bx2 bxS bxN fst snd]; [reflexivity | lia | lia | reflexivity].
Qed.
Lemma HC0 : ltac2:(tb__ "0|1|
S1aS6S81Z0S49S4S4S0S0A2M0S0A2G0SaG0S0A2VFF;A4A2U0A3"). Proof. apply HCEN. cbn. tauto. Qed.
Lemma HC1 : ltac2:(tb__ "0|1|
S1aS6S81Z1S49S4S4S0S0A2M0S0A2G0SaG0S0A2VFF;A4A2U0A3"). Proof. apply HCEN. cbn. tauto. Qed.
Lemma HC3 : ltac2:(tb__ "0|1|
S1aS6S81Z3S49S4S4S0S0A2M0S0A2G0SaG0S0A2VFF;A4A2U0A3"). Proof. apply HCEN. cbn. tauto. Qed.
Lemma HC5 : ltac2:(tb__ "0|1|
S1aS6S81Z5S49S4S4S0S0A2M0S0A2G0SaG0S0A2VFF;A4A2U0A3"). Proof. apply HCEN. cbn. tauto. Qed.
Lemma HC6 : ltac2:(tb__ "0|1|
S1aS6S81Z6S49S4S4S0S0A2M0S0A2G0SaG0S0A2VFF;A4A2U0A3"). Proof. apply HCEN. cbn. tauto. Qed.

Lemma box_in : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S37S19S2VJAv;S56A1S8bR3R2R1A6S19S2VJAvL;S2bS91S41S5dS29A4A1S8bR4R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (BXok_d_pair _ BX HBX) as [V0 K0]. destruct (bd_proL_sums rho) as (Swp & Snn & SV & SK).
  apply (SPA_rebox AInv CST XGL NP Kc rho0 P0 FB FF PTrue BX BXL [blkAR] fr_lo bd_pro bd_proL ANone E_blr0 rho tp w); [| | | |exact Swp| |exact Hw];
    unfold BXL, bxV, bxK, cE, kE, KU in *; cbn [bx2 bxS bxN fst snd]; try lia.
  intros _ _. split; [exact Snn|]. unfold cE, kE, KU in *. lia.
Qed.

Lemma after_box : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S37S19S2VJAvL;S2dA1S58R3R2R1A6S19S2VJAv;S86A1S58R4R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (BXok_d_pair _ BX HBX) as [V0 K0].
  apply (SPA_box_out AInv CST XGL NP Kc rho0 P0 FB FF PTrue BX BXL cE kE tvL frL [LA A1; LAK AK1] bd_rest (AHead pH true) K_after0 rho tp w);
    [| | | | | | | |exact Hw]; unfold BXL, bxV, bxK, cE, kE, KU in *; cbn [bx2 bxS bxN fst snd]; lia.
Qed.
Lemma after_step : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S37S19S2VJAFvL;S39S2dA2S8aR3R2R1A6S1bS89R4A1S19S2VJAv;S86A1S58R4R3R2A6A2F_;Fw;Ftp;Frho;").
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
SeS5S1eQ40A1A1S37S1bS1aS0S5eR3S13P191A1A2Z0M0A3S1aS0S5eR3S13P19aA1A2G0A3A2S19S2VJAFvL;S39S2dA2S58R4R3R2A6S1bS89R5A1S19S2VJAv;S86A1S58R5R4R3A6A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w [Z1 Z2] Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblL ndA1 K_after0 rho tp w Hw) as [HS HT].
  split; [|exact (after_box rho tp w HS)]. apply (ldefR_intro rho (proj2 HT)).
  pose proof (uval_range rho pNX) as RN.
  constructor; [unfold fact_nv, vNV; rewrite h_ule, Z1; lia|]. constructor; [unfold fact_nt; rewrite h_ule, Z2; lia | constructor].
Qed.

Lemma body_step : ltac2:(tb__ "0|4|
SeS5S1eQ40A1A1S37S19S2VJAFvL;S39S2dA2S71R3R2R1A6S1dSeSeS1bS1bS38R1A1S1bS42Z0S4bS3S4S4S1fS21A2M0S6A2M1S4S0SfA2M2S3G0S6S3S1fS21S76S2dA4U1A4S3S0SfS2eS2fZ18S55A2A4A4R1A2M3A2S44G3S4bS3G1G2S3G0S6S3S1fS21S71S2dA4U0A4S3S0SfS2eS2fZ19S55A2A4A4R5A2A2A2A2S19S2VJAvL;S2dA1S76R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblL ndA1 X_bodyN rho tp w Hw) as [HS HT].
  pose proof s5_checks_loop as (C1 & C2 & C3 & _). pose proof s5_checks_meas as (M1 & M2 & M3 & _).
  destruct (meas_facts X_bodyN rho M1 M2 M3 (smatchA_facts segs rho tp X_bodyN w (proj1 HS))) as [Hi Hc].
  destruct (body_carve AInv CST XGL ALA HCST HXGL Kc HKc FB FF BXL PTrue rho0 (bdA A1) (AHead pH true) rho tp w C1 C2 C3 HT HS) as (rho2 & HB & HS2 & EC & EI).
  exists rho2. split; [split; [exact HB|] | exact HS2].
  exact (meas_same rho rho2 25 24 X_bodyN K_body ndA1 ndA1 0%nat 1%nat EI EC Hi Hc ltac:(lia) ltac:(lia)).
Qed.
Lemma latch_step : ltac2:(tb__ "0|4|
SeS5S1eQ40A1A1S37S19S2VJAFvL;S38S30A2S70R3R2R1A6S1dSeSeS1bS1bS39R1A1S1bS42Z0S4bS3S4S4S1fS21A2M0S6A2M1S4S0SfA2M2S3G0S6S3S1fS21S77S2dA4U0A4S3S0SfS2eS2fZ1aS55A2A4A4R1A2M3A2S44G3S4bS3G1G2S3G0S6S3S1fS21S70S30A4U1A4S3S0SfS2eS2fZ1S55A2A4A4R5A2A2A2A2S19S2VJAvL;S2dA1S77R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblB ndX0 X_latch rho tp w Hw) as [HS HB].
  pose proof s5_checks_loop as (_ & _ & _ & C1 & C2 & C3).
  destruct (latch_absorb2 AInv CST XGL ALA HCST HXGL Kc HKc FB FF BXL PTrue rho0 (bdX 0) (bdA A1) (AHead pH true) rho tp w C1 C2 C3 HB HS)
    as (rho2 & HT & HS2 & EC & EI & Hi & Hc).
  exists rho2. split; [split; [exact HT|] | exact HS2].
  exact (meas_latch rho rho2 1 26 X_latch K_loop ndX0 ndA1 1%nat 0%nat EI EC Hi Hc ltac:(lia) ltac:(lia)).
Qed.
Lemma dp_step : ltac2:(tb__ "0|6|
SeS5S1eQ40A1A1S37S19S2VJAFvL;S38S2dA2S94R3R2R1A6S1dS1fS1fS1bS1bS5aS4S4S4S1fS21A2M0S6A2M1S4S0SfA2M2A2S3G1G2S3G0S6S3S1fS21R1S2dA4U1M3A4S3S0SfS2eS2fZ14S55A2A4A4M4S84A3S1bS38R5A1S1bS42Z0S4bG4R5A2M5A2S44G5S4bS3G1G2S3G0S6S3S1fS21S94S2dA4G3A4S3S0SfS2eS2fZ15S55A2A4A4R5A2A2A2A2A2S19S2VJAvL;S2dA1R1R5R4R3A6A2LT;A2F_;Fw;Ftp;Frho;").
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
S42S66VBXL;A1S66VBX;A1A2"). Proof. unfold BXL. cbn [bxS]. lia. Qed.
Lemma HBN : ltac2:(tb__ "0|0|
S42S65VBXL;A1S65VBX;A1A2"). Proof. unfold BXL. cbn [bxN]. lia. Qed.
Lemma HBV : ltac2:(tb__ "0|0|
S42S67VBX;A1S67VBXL;A1A2"). Proof. unfold BXL, bxV, cE. cbn [bx2 fst]. lia. Qed.
Lemma HBK : ltac2:(tb__ "0|0|
S42S45S64VBX;A1S46Z14S60A2A2S64VBXL;A1A2"). Proof. unfold BXL, bxK, kE, KU. cbn [bx2 snd]. lia. Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S2cS2VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S7aS2S79VAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S0S5aS0R1S9S0Z0S9S0Zf5S9S0Zf8SbS0A1A3A3A3A3SadS2S79VAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48 : ltac2:(tb__ "0|0|
S9aS2S79VAInv;VCST;VXGL;S99A6").
Hypothesis MCROM : ltac2:(tb__ "0|0|
S9dS2S79VAInv;VCST;VXGL;S9cZcA7").
Variable Q : assn.
Hypothesis XPK_T : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S36S2Vok;S19S2VJAv;Sa5A1Sa2R2R1A5VQ;A4Ftp;Frho;").
Hypothesis XPE_T : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S36S2Vok;S19S2VJAv;Sa4A1Sa1R2R1A5VQ;A4Ftp;Frho;").

Lemma KDISP_T : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S3bR2A1S36S2Vok;S19S2VJAv;Sa0A1S9fR3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HL.
  exact (EP.epiDE_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC MC48 (fun _ => Q)
           (fun rho tp _ => XPK_T rho tp) (fun rho tp _ => XPE_T rho tp) rho tp [] HL).
Qed.
Lemma AFTER_T : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S89R2A1S36S2Vok;S19S2VJAv;S86A1S58R3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HL.
  exact (EP.epi_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC MC48 (fun _ => Q)
           (fun rho tp _ => XPK_T rho tp) (fun rho tp _ => XPE_T rho tp) rho tp [] HL).
Qed.

Let QA : assn := ltac2:(tb__ "0|0|
S37S1cS93S2S49S4eS97S52VAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBXL;S22S82AcS49S4dS4eS50S83A4A4R1A3VQ;R1A1A2Lw;").
Let QB : assn := ltac2:(tb__ "0|0|
S37S1cS93S2S49S4eS97S52VAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBXL;S22S85AcS49S4dS4eS50S84A4A4R1A3VQA;R1A1A2Lw;").

Lemma XLa_T : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S36S2Vok;S19S2VJAFvL;S38S30A2S70R2R1A5VQA;A4Ftp;Frho;").
Proof.
  intros rho tp. eapply triple_conseq; [intros w Hw; exact (latch_step rho tp w Hw) | intros w Hw; exact Hw |].
  apply triple_ex. intros rho2. apply triple_pure. intros [HT _].
  exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue PhisA ok (map efdrop cutsA) K_loop ndA1 0%nat Q rho2 tp ltac:(left; reflexivity) HT).
Qed.
Lemma XL_T : ltac2:(tb__ "0|1|
SeS5S1eQ40A1A1M0G0S36S2Vok;S19S2VJAFvL;S38S30A2S70R3R2A5VQB;A4Ftp0;Ftp;Frho;").
Proof. intros rho tp _. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLa_T rho tp)]. Qed.

Lemma XLE2_T : ltac2:(tb__ "0|1|
SeS5S1eQ40A1A1M0G0S36S2Vok;S19S2VJAFvL;S38S31A2S80R3R2A5VQB;A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp _. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errL2_T AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 ok Hok Q KDISP_T rho tp).
Qed.
Lemma XLE2f_T : ltac2:(tb__ "0|1|
SeS5S1eQ40A1A1M0G0S36S2Vok;S19S2VJAFvL;S38S95A2S80R3R2A5VQB;A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp _. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errLf_T AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBS HBN HBV HBK rho0 ok Hok Q KDISP_T rho tp).
Qed.
Lemma XLE1_T : ltac2:(tb__ "0|1|
SeS5S1eQ40A1A1M0G0S36S2Vok;S19S2VJAFvL;S38S31A2S73R3R2A5VQB;A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp _. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errL1_T AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 ok Hok Q KDISP_T rho tp).
Qed.

Lemma B_T : ltac2:(tb__ "0|3|
S1fS21S6S4S0SfA2M0SeS5S1eQ40A1A1S5aS4S4S4S1fS21A2M1S6A2M2G0A2S3G2G0S3G1S6S3S1fS21R6R5A4R4A4R3A4S84A3S4fS85R5R3A3S36S2Vok;S19S2VJAvL;R7A1R8R4R3A5VQA;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisB k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisB PhisA_reads H_ecertB_ok FUEL_B cps_B NP cutsB exitsB ok QA Hok
           ecertB_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn [efdrop fst] in E. injection E as <- <- <-.
  unfold exitsB, h_exits, us_exits in HinX. cbn [map app In] in HinX.
  destruct HinX as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <- <- <-.
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_avn_pf.arm_vn_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC0 ok Hok AC (fun _ => QB) XL_T XLE1_T rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_avt_pf.arm_vt_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 ok Hok AC (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_af_pf.arm_f_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC3 HC6 ok Hok AC SSC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_pf.handle_f_ok (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_load_obj_al_pf.arm_l_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 ok Hok AC (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_ap_pf.arm_p_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC0 ok Hok AC (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aml_pf.arm_ml_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 HCFG ok Hok AC (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_ago_pf.arm_go_T AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BXL HBXL rho0 ok Hok AC (fun _ => QB) XL_T XLE2f_T rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_as_pf.arm_s_T AInv CST XGL ALA Kc HKc FB FF BXL rho0 ok Hok (fun _ => QB) XL_T rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aus_pf.arm_us_T AInv CST XGL ALA Kc HKc FB FF BXL rho0 ok Hok (fun _ => QB) XL_T rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aus_pf.arm_us0_T AInv CST XGL ALA Kc HKc FB FF BXL rho0 ok Hok (fun _ => QB) XL_T rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv_pf6.arm_v_T AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BXL HBXL rho0 ok Hok AC MCROM (fun _ => QB) XL_T XLE2_T rho1 tp1 []).
  - exact (XL_T rho1 tp1 []).
Qed.

Lemma A_T : ltac2:(tb__ "0|3|
S1fS21S6S4S0SfA2M0SeS5S1eQ40A1A1S5aS4S4S4S1fS21A2M1S6A2M2G0A2S3G2G0S3G1S6S3S1fS21R6R5A4R4A4R3A4S83A3S4fS82R5R3A3S36S2Vok;S19S2VJAvL;R7A1R8R4R3A5VQ;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
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
SeS5S1eQ40A1A1S39R2A1S36S2Vok;S19S2VJAFvL;S39S2dA2S71R3R2A5VQ;A4F_;Ftp;Frho2;").
Proof.
  intros rho2 tp _. eapply triple_conseq; [intros w Hw; exact (body_step rho2 tp w Hw) | intros w Hw; exact Hw |].
  apply triple_ex. intros rho3. apply triple_pure. intros [HB _].
  exact (A_T K_body ndA1 1%nat (RL, VLA 24 z0) rho3 tp ltac:(right; left; reflexivity) HB).
Qed.
Lemma TGT_after0_T : ltac2:(tb__ "0|1|
SeS5S1eQ40A1A1S39R2A1S1bS1aS0S5eR3S13P191A1A2Z0M0A3S1aS0S5eR3S13P19aA1A2G0A3A2S36S2Vok;S19S2VJAFvL;S39S2dA2S58R4R3A5VQ;A4F_;F_;Ftp;Frho2;").
Proof.
  intros rho2 tp _ HZ. eapply triple_conseq; [intros w Hw; exact (after0_step rho2 tp w HZ Hw) | intros w Hw; exact Hw |].
  apply triple_pure. intros HL. exact (AFTER_T rho2 tp HL).
Qed.
Lemma CONT_blr_T : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S36S2Vok;S19S2VJAv;S56A1S8bR2R1A5VQ;A4Ftp;Frho;").
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
S5S1eQ40A1A1S36S2Vok;S19S2VJAv;Sa3A1S7eVrho0;R1A5VQ;A4Ftp0;").
Proof.
  intros tp0.
  exact (PP.pro_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 HC5 ok Hok AC SSC MC48 Q CONT_blr_T XPE_T tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S7bS2S79VAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S0S5aS0R1S9S0Z0S9S0Zf5S9S0Zf8SbS0A1A3A3A3A3SaeS2S79VAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48X : ltac2:(tb__ "0|0|
S9bS2S79VAInv;VCST;VXGL;S99A6").
Hypothesis MCROMX : ltac2:(tb__ "0|0|
S9eS2S79VAInv;VCST;VXGL;S9cZcA7").
Variable Q : world -> Prop.
Hypothesis XPK_E : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S35S2S19S2VJAv;Sa5A1Sa2R2R1A5VQ;A3Ftp;Frho;").
Hypothesis XPE_E : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S35S2S19S2VJAv;Sa4A1Sa1R2R1A5VQ;A3Ftp;Frho;").

Lemma KDISP_E : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S3bR2A1S35S2S19S2VJAv;Sa0A1S9fR3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HL.
  exact (EP.epiDE_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX MC48X (fun _ _ => Q) (fun _ _ _ _ _ H => H)
           (fun rho tp _ => XPK_E rho tp) (fun rho tp _ => XPE_E rho tp) rho tp [] HL).
Qed.
Lemma AFTER_E : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S89R2A1S35S2S19S2VJAv;S86A1S58R3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HL.
  exact (EP.epi_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX MC48X (fun _ _ => Q) (fun _ _ _ _ _ H => H)
           (fun rho tp _ => XPK_E rho tp) (fun rho tp _ => XPE_E rho tp) rho tp [] HL).
Qed.

Let QAe (b : Z) : world -> Prop := ltac2:(tb__ "0|0|
S37S1cS92S2S49S4dS96S51VAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBXL;S22S82AcS83A4Vb;R1A4VQ;R1A1A2Lw;").
Let QBe (b : Z) : world -> Prop := ltac2:(tb__ "0|0|
S37S1cS92S2S49S4dS96S51VAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBXL;S22S85AcS84A4Vb;R1A4VQAe;Vb;R1A2A2Lw;").
Let FAMB : Z -> list word -> assn := fun b _ => QBe b.
Lemma QAe_mono : ltac2:(tb__ "0|0|
S0S0S37S42R3R2A2VQAe;R4R2A2VQAe;R4R3A2F_;F_;Fw;Fb';Fb;").
Proof. intros b b' w Hb [H|H]; [left; exact (SPfamETA_mono _ b b' w Hb H) | right; exact H]. Qed.
Lemma FAMB_mono : ltac2:(tb__ "0|0|
S0S0S5S1eQ40A1A1S37S42R4R3A2VFAMB;R5R3R2A3VFAMB;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Proof. intros b b' tp0 w Hb [H|H]; [left; exact (SPfamETA_mono _ b b' w Hb H) | right; exact (QAe_mono b b' w Hb H)]. Qed.

Lemma XLa_E : ltac2:(tb__ "0|1|
SeS5S1eQ40A1A1S35S2S19S2VJAFvL;S38S30A2S70R2R1A5VQAe;S4bS3S4S4S1fS21A2M0S6A2S4S0SfA2S3G0S6S3S1fS21S70S30A4U1A4S3S0SfS2eS2fZ1S55A2A4A4R2A2A1A3Ftp;Frho;").
Proof.
  intros rho tp. eapply etriple_conseq; [intros w Hw; exact (latch_step rho tp w Hw) | intros w Hw; exact Hw |].
  apply etriple_ex. intros rho2. apply etriple_pure. intros [HT HM].
  exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue PhisA cutsA K_loop ndA1 0%nat (RL, VLA 26 z0) Q _ rho2 tp ltac:(left; reflexivity) HT HM).
Qed.
Lemma XL_E : ltac2:(tb__ "0|2|
SeS5S1eQ40A1A1M0G0S35S2S19S2VJAFvL;S38S30A2S70R3R2A5VFAMB;S4bS3S4S4S1fS21A2M1S6A2S4S0SfA2S3G1S6S3S1fS21S70S30A4U1A4S3S0SfS2eS2fZ1S55A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLa_E rho tp)]. Qed.
Lemma XLE2_E : ltac2:(tb__ "0|2|
SeS5S1eQ40A1A1M0G0S35S2S19S2VJAFvL;S38S31A2S80R3R2A5VFAMB;S4bS3S4S4S1fS21A2M1S6A2S4S0SfA2S3G1S6S3S1fS21S80S31A4U1A4S3S0SfS2eS2fZ1S55A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errL2_E AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 Q KDISP_E rho tp).
Qed.
Lemma XLE2f_E : ltac2:(tb__ "0|2|
SeS5S1eQ40A1A1M0G0S35S2S19S2VJAFvL;S38S95A2S80R3R2A5VFAMB;S4bS3S4S4S1fS21A2M1S6A2S4S0SfA2S3G1S6S3S1fS21S80S95A4U1A4S3S0SfS2eS2fZ1S55A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errLf_E AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBS HBN HBV HBK rho0 Q KDISP_E rho tp).
Qed.
Lemma XLE1_E : ltac2:(tb__ "0|2|
SeS5S1eQ40A1A1M0G0S35S2S19S2VJAFvL;S38S31A2S73R3R2A5VFAMB;S4bS3S4S4S1fS21A2M1S6A2S4S0SfA2S3G1S6S3S1fS21S73S31A4U1A4S3S0SfS2eS2fZ1S55A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; right; exact Hw |].
  exact (CE.errL1_E AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX BXL HBX HBXL HBS HBN HBV HBK rho0 Q KDISP_E rho tp).
Qed.

Lemma B_E : ltac2:(tb__ "0|3|
S1fS21S6S4S0SfA2M0SeS5S1eQ40A1A1S5aS4S4S4S1fS21A2M1S6A2M2G0A2S3G2G0S3G1S6S3S1fS21R6R5A4R4A4R3A4S84A3S4fS85R5R3A3S35S2S19S2VJAvL;R7A1R8R4R3A5VQAe;S4bS3G2G0S3G1S6S3S1fS21R8R7A4R6A4R5A4R4A2A1A3F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisB k) nd T rho tp _ Hphi).
  refine (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisB PhisA_reads H_ecertB_ok FUEL_B cps_B NP cutsB exitsB QAe QAe_mono ecertB_ok _ T nd k rv rho tp Hin).
  intros X ndX kX rvX rho1 tp1 HinX.
  unfold exitsB, h_exits, us_exits in HinX. cbn [map app In] in HinX.
  destruct HinX as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <- <- <-.
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_avn_pf.arm_vn_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC0 ACX FAMB FAMB_mono XL_E XLE1_E rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_avt_pf.arm_vt_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 ACX FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_af_pf.arm_f_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC3 HC6 ACX SSCX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_pf.handle_f_ok_ex FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f8.Lib_load_obj_al_pf.arm_l_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 ACX FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_ap_pf.arm_p_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC0 ACX FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aml_pf.arm_ml_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BXL HBXL rho0 HC1 HCFG ACX FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_ago_pf.arm_go_E AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BXL HBXL rho0 ACX FAMB FAMB_mono XL_E XLE2f_E rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_as_pf.arm_s_E AInv CST XGL ALA Kc HKc FB FF BXL rho0 FAMB FAMB_mono XL_E rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aus_pf.arm_us_E AInv CST XGL ALA Kc HKc FB FF BXL rho0 FAMB FAMB_mono XL_E rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aus_pf.arm_us0_E AInv CST XGL ALA Kc HKc FB FF BXL rho0 FAMB FAMB_mono XL_E rho1 tp1 []).
  - exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv_pf6.arm_v_E AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BXL HBXL rho0 ACX MCROMX FAMB FAMB_mono XL_E XLE2_E rho1 tp1 []).
  - exact (XL_E rho1 tp1 []).
Qed.

Lemma A_E : ltac2:(tb__ "0|3|
S1fS21S6S4S0SfA2M0SeS5S1eQ40A1A1S5aS4S4S4S1fS21A2M1S6A2M2G0A2S3G2G0S3G1S6S3S1fS21R6R5A4R4A4R3A4S83A3S4fS82R5R3A3S35S2S19S2VJAvL;R7A1R8R4R3A5VQ;A3F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
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
SeS5S1eQ40A1A1S39R2A1S35S2S19S2VJAFvL;S39S2dA2S71R3R2A5VQ;A3F_;Ftp;Frho2;").
Proof.
  intros rho2 tp _. eapply etriple_conseq; [intros w Hw; exact (body_step rho2 tp w Hw) | intros w Hw; exact Hw |].
  apply etriple_ex. intros rho3. apply etriple_pure. intros [HB _].
  exact (A_E K_body ndA1 1%nat (RL, VLA 24 z0) rho3 tp ltac:(right; left; reflexivity) HB).
Qed.
Lemma TGT_after0_E : ltac2:(tb__ "0|1|
SeS5S1eQ40A1A1S39R2A1S1bS1aS0S5eR3S13P191A1A2Z0M0A3S1aS0S5eR3S13P19aA1A2G0A3A2S35S2S19S2VJAFvL;S39S2dA2S58R4R3A5VQ;A3F_;F_;Ftp;Frho2;").
Proof.
  intros rho2 tp _ HZ. eapply etriple_conseq; [intros w Hw; exact (after0_step rho2 tp w HZ Hw) | intros w Hw; exact Hw |].
  apply etriple_pure. intros HL. exact (AFTER_E rho2 tp HL).
Qed.
Lemma CONT_blr_E : ltac2:(tb__ "0|0|
SeS5S1eQ40A1A1S35S2S19S2VJAv;S56A1S8bR2R1A5VQ;A3Ftp;Frho;").
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
S5S1eQ40A1A1S35S2S19S2VJAv;Sa3A1S7eVrho0;R1A5VQ;A3Ftp0;").
Proof.
  intros tp0.
  exact (PP.pro_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 HC5 ACX SSCX MC48X (fun _ _ => Q) (fun _ _ _ _ _ H => H)
           (fun rho tp _ => CONT_blr_E rho tp) (fun rho tp _ => XPE_E rho tp) tp0).
Qed.
End Existence.
End Sum.

Theorem load_obj_ok : IF.load_obj_stmt.
Proof.
  intros AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC MC48 MCROM tp0.
  eapply triple_conseq; [intros w Hw; exact (JA_pre_intro segs AInv CST XGL NP Kc (IF.P0_los CST FB FF) FB FF BX PTrue rho0 IF.nd_lo0 Pre_lo tp0 w Hw) | intros w Hw; exact Hw |].
  apply (TRs_pureP segs ok _ (IF.P0_los CST FB FF rho0)).
  { intros w Hw. exact (SPA_JA_P0_get AInv CST XGL NP Kc rho0 (IF.P0_los CST FB FF) FB FF PTrue BX IF.nd_lo0 Pre_lo rho0 tp0 w Hw). }
  intros HP0s. pose proof HP0s as (HP0 & HCFG & HCEN).
  eapply triple_conseq; [intros w Hw; exact (SPA_JA_P0_set AInv CST XGL NP Kc rho0 (IF.P0_los CST FB FF) FB FF PTrue (P0_lo CST FB FF) BX IF.nd_lo0 Pre_lo rho0 tp0 w HP0 Hw) | intros w Hw; exact Hw |].
  apply (lo_body_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 HCFG HCEN ok Hok AC SSC MC48 MCROM
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

Theorem load_obj_ok_ex : IF.load_obj_stmt_ex.
Proof.
  intros AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX MC48X MCROMX tp0.
  eapply etriple_conseq; [intros w Hw; exact (JA_pre_intro segs AInv CST XGL NP Kc (IF.P0_los CST FB FF) FB FF BX PTrue rho0 IF.nd_lo0 Pre_lo tp0 w Hw) | intros w Hw; exact Hw |].
  apply (TRe_pureP segs _ (IF.P0_los CST FB FF rho0)).
  { intros w Hw. exact (SPA_JA_P0_get AInv CST XGL NP Kc rho0 (IF.P0_los CST FB FF) FB FF PTrue BX IF.nd_lo0 Pre_lo rho0 tp0 w Hw). }
  intros HP0s. pose proof HP0s as (HP0 & HCFG & HCEN).
  eapply etriple_conseq; [intros w Hw; exact (SPA_JA_P0_set AInv CST XGL NP Kc rho0 (IF.P0_los CST FB FF) FB FF PTrue (P0_lo CST FB FF) BX IF.nd_lo0 Pre_lo rho0 tp0 w HP0 Hw) | intros w Hw; exact Hw |].
  apply (lo_body_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 HCFG HCEN ACX SSCX MC48X MCROMX
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
