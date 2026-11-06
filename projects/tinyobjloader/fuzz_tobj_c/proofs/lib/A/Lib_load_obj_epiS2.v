(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "true"; "false"; "nil"; "pair"; "app"; "prod"; "fst"; "option"; "list"; "S"; "andb"; "negb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "ASv"; "BI"; "BIc"; "bd_subst"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "leafA"; "entailsA"; "ax_X"; "la_reason"; "la_state"; "ax_setS"; "list_eqb"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sobj"; "SLit"; "ss_facts"; "sv"; "sprop"; "sv_eqb"; "cell"; "ss_next"; "valuation"; "ss_pc"; "mkObj"; "ob_base"; "ob_lo"; "ss_objs"; "DUnknown"; "SAlu"; "SPUle"; "c_off"; "c_width"; "mkCell"; "mkSS"; "ob_cells"; "ob_dflt"; "ob_hi"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.AD"; "Pre_ad"; "P_ok"; "P_fail"; "nd0"; "ndK"; "CH"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "optL"; "vDp"; "vOUT"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "DUPk"; "DUPv"; "B_1"; "blk_chk"; "dupAt"; "ent_chk2"; "skipL"; "s_ad"; "T_ad0"; "bd_com"; "cAt"; "cps_b"; "kAt"; "ndAt"; "B_2"; "B_3"; "B_4"; "B_5"; "B_6"; "B_7"; "PDk_ad"; "R_ad"; "bdAt"; "xfb_ad"; "ENDOWs"; "E_ad"; "E_adF"; "L_v0a"; "L_v0b"; "T_adB"; "Xk_ad"; "bnds"; "brestAt"; "callL"; "go_fact"; "hand_ad"; "pc_cf"; "pc_vf0"; "set_objs"; "xf_ad"; "B32m"; "Ls_succ"; "gen_err"; "gen_out"; "iW"; "pcs_b"; "vERRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "nd_am"; "am_subst"; "NDA"; "nd_tv"; "AHead"; "AK0"; "AV0"; "am_eqb"; "nd_bd"; "nd_below"; "nd_fr"; "fr_sub_eqb"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "mul"; "of_nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "runL"; "leafL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "bud_pay2"; "@Stdlib.Lists.List"; "forallb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.AD.ADAddr"; "ad_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "bA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "blkAR"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pdescA"; "T_afterA3"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "bd_rest"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "junkR"; "pc_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1"; "EK"; "EV"; "cE"; "cps_s"; "kE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "oidx"; "s1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ef.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
Module AD. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup. End AD. Module ADP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ef.Lib_arena_dup_pf. End ADP.

Definition pc_cf : Z := 0x8ed7c.
Definition pc_vf0 : Z := 0x8e9e4.
Definition pcs_b : list Z := ltac2:(tb__ "0|0|
S0SfZ8ea64S0SfZ8eae0S0SfZ8eb5cS0SfZ8ebd8S0SfZ8ec54S0SfZ8ecd0S5SfA1A3A3A3A3A3A3").
Definition cps_b : list Z := ltac2:(tb__ "0|0|
S0SfS78S0SfS79S7SfS81Sc0A3A3A3").
Definition set_objs (A : axst) (os : list sobj) : axst := ltac2:(tb__ "0|0|
S19VA;A1S43S20VA;S39S2eR1A1S41R1A1S3fR1A1S3eR1A1S42R1A1Vos;S27R1A1S2cR1A1S40R1A1A9A2TS;").
Definition gen_out (A : axst) : axst := ltac2:(tb__ "0|1|
S7aVA;S4cS25S25S25S1S25L_;SdS2aS30R1A1S52A2S2aS31R1A1S26Z0A1M0A2A2S2fS52G0S26Zd0A1S5S2bA1S33A5R1X1x2Lo;S32S19VA;A1A1A4A2").
Definition vERRq : sv := SVar 461.
Definition gen_err (A : axst) : axst := ltac2:(tb__ "0|4|
S7aVA;S4cS25S25S25S1S25L_;SdS2aS30R1A1M0SacA2S2aS31R1A1M1S26Z60A1M2A2A2S2fG0G1S3cR1A1S4cS2bS2bS2bS1S2bL_;S2aS36R1A1M3G2A2S38G3S37R1A1S82A3R1X1x2Lc;S3aR1A1A4S3bR1A1A5R1X1x2Lo;S32S19VA;A1A1A4A2").
Definition B32m : Z := 4294967295.
Definition bnds : list sprop := ltac2:(tb__ "0|0|
S4cS10S29S10S35S24R1A1S26S7cA1A2Lv;S0S10P191S0S10P197S0S10P19aS0S10P1a3S5S10A1A3A3A3A3A4").
Definition junk_cs : list nat := ltac2:(tb__ "0|0|
S0S2U1S0S2U6S0S2U7S0S2UaS0S2UbS0S2UcS0S2UdS0S2UeS0S2UfS0S2U10S0S2U11S0S2U1cS0S2U1dS0S2U1fS5S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition Ls_succ : list leafA := Eval vm_compute in runL 300 cps_b K_succ.
Definition L_v0a : axst := Eval vm_compute in leafL Ls_succ pc_vf0 0.
Definition L_v0b : axst := Eval vm_compute in leafL Ls_succ pc_vf0 1.
Definition L_cf0 : axst := Eval vm_compute in leafL Ls_succ pc_cf 0.
Definition cnz : sprop := SPBranch BC_NE (SVar 416) (SLit 0).
Definition K_vf0 : axst := Eval vm_compute in junkR [11]%nat (ax_with_facts L_v0a (List.filter (fun f => negb (sprop_eqb f cnz)) (ss_facts (ax_S L_v0a)))).

Definition B_1 : axst := Eval vm_compute in ax_add_facts bnds (gen_err (gen_out (junkR [1; 20]%nat K_vf0))).
Definition nextBj (jl : list nat) (L : axst) : axst := ltac2:(tb__ "0|0|
Sc5S7eS7fSbaVjl;VL;A2A1A1S27S19S56A1A1A2").
Definition nextB (L : axst) : axst := nextBj junk_cs L.
Definition skipL (B : axst) (pc : Z) : axst := ltac2:(tb__ "0|0|
S9dS9cU12cS5fVB;A3Vpc;U0A3").
Definition callL (B : axst) : axst := ltac2:(tb__ "0|0|
S9dS9cU12cS5fVB;A3SaaU0A3").
Definition B_2 : axst := Eval vm_compute in nextB (skipL B_1 0x8ea64).
Definition B_3 : axst := Eval vm_compute in nextB (skipL B_2 0x8eae0).
Definition B_4 : axst := Eval vm_compute in nextB (skipL B_3 0x8eb5c).
Definition B_5 : axst := Eval vm_compute in nextB (skipL B_4 0x8ebd8).
Definition B_6 : axst := Eval vm_compute in nextB (skipL B_5 0x8ec54).

Definition B_7 : axst := Eval vm_compute in nextBj (5%nat :: junk_cs) (skipL B_6 0x8ecd0).

Definition iW (A : axst) : nat := ltac2:(tb__ "0|0|
Sc2Sc3S51VA;A3").
Definition xf_ad (A : axst) : list axform := ltac2:(tb__ "0|2|
S0S83S88S80VA;A1M0S26N40M1A1A2S0S83S85G0G1A2S5S83A1A3A3").
Definition go_fact (d : sv) : sprop := SPUle (SLit 4096) d.
Definition E_adF (E0 : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
Sa2S0S29S76Vd;A1S5S29A1A3VE0;A2").
Definition E_ad (E0 : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S50S84S6eVE0;Vd;A2S7bVE0;A1A2A1").
Definition s_ad (E : axst) : wsub := ltac2:(tb__ "0|0|
S0S8S10S28A2S6S10S28P13S34Sb8S51S26Z40A1A3A4S9ePaS19VE;A1S19S46A1A3A3").
Definition R_ad (E : axst) : list sobj := ltac2:(tb__ "0|0|
S53Sa3VE;S46S5bVE;A1A3A1").
Definition Xk_ad (E : axst) (d : sv) : list (sv * sv) := ltac2:(tb__ "0|2|
Sa9S8S28S28A2M0G0SdSeS2aS9S28S28R1A3M1SafA2A1SeS2aG1Vd;A2A1A2Lr;S1dVE;A1A3").
Definition hand_ad (E : axst) : list bitem := ltac2:(tb__ "0|0|
S16S5bVE;A1S4bA2").
Definition PDk_ad : list pdescK := liftPD ADP.PD_ad.
Definition xfb_ad (T : axst) : list axform := ltac2:(tb__ "0|3|
S0S83S85U1M0Z40A2S0S83S87S0S2G0S0S2U0M1S4eU2M2S9fSbcVT;A1G2A2A2A3A3A1S0S83S86G1A1S5S83A1A3A3A3").
Definition T_ad0 (E : axst) (d : sv) (P : axst) : axst := ltac2:(tb__ "0|0|
Sb3S46VE;S5bVE;A1S69VE;A1VP;S72VE;Vd;A2A6").
Definition T_adB (T0 : axst) : axst := ltac2:(tb__ "0|0|
S50S84VT0;S6bVT0;A1A2A1").

Definition DUPv (a b c d k : Z) : bitem := ltac2:(tb__ "0|1|
S14Z1Z0S0S8SfS12A2M0S6SfS12Va;S13S24P191A1A1A4S0G0S6SfS12Vb;S13S24P197A1A1A4S0G0S6SfS12Vc;S13S24P19aA1A1A4S0G0S6SfS12Vd;S13S24P1a3A1A1A4S5G0A1A3A3A3A3Vk;A4").
Definition DUPk (a b c d k : Z) : bitem := ltac2:(tb__ "0|1|
S14Z0Z1S0S8SfS12A2M0S6SfS12Va;S13S24P191A1A1A4S0G0S6SfS12Vb;S13S24P197A1A1A4S0G0S6SfS12Vc;S13S24P19aA1A1A4S0G0S6SfS12Vd;S13S24P1a3A1A1A4S5G0A1A3A3A3A3Vk;A4").
Definition bd_com (c k : Z) : list bitem := ltac2:(tb__ "0|0|
S0S11SbeVc;A1S0S11SbdVk;A1S4dS11U26Sb9A3A3A3").
Definition kept_ad : list (sv * sv) := removelast tvL.

Definition dupAt (j : nat) : list bitem := ltac2:(tb__ "0|a|
S2SbS11A1M0Lj;Vj;S0S11S55Z0M1G1G1Z100M2Zc0A5S0S11S54G1G1G1Z200M3Z80A5S5S11A1M4A3A3M5S2S2G0Ln;R1S0S11S55Z38Z8M6Z18M7G2Z310A5S0S11S54Z70Z10M8Z30M9G3Z220A5G4A3A3S2S2G0Ln0;R1S0S11S55Z20G6G7G2Z2b0A5S0S11S54Z40G8G9G3Z1e0A5G4A3A3S2S2G0Ln1;R1S0S11S55G7G6G7G2Z250A5S0S11S54G9G8G9G3Z1a0A5G4A3A3S2S2G0Ln2;R1S0S11S55G7G1G7G2Z1f0A5S0S11S54G9G1G9G3Z160A5G4A3A3S2S2G0Ln3;R1S0S11S55G7G1G6G2Z190A5S0S11S54G9G1G8G3Z120A5G4A3A3S2S2G0Ln4;R1S0S11S55G7G1G1G2Z130A5S0S11S54G9G1G1G3Ze0A5G4A3A3S2G5Ln5;X2x2Ln4;X2x2Ln3;X2x2Ln2;X2x2Ln1;X2x2Ln0;X2x2Ln;X2x2").
Definition cAt (j : nat) : Z := ltac2:(tb__ "0|0|
S96S96S96SbfZ362A2Z100A2S97S98S9fVj;U1A2A1S90A2A2").
Definition kAt (j : nat) : Z := ltac2:(tb__ "0|0|
S96S96S96Sc1Z44A2Z200A2S97S98S9fVj;U1A2A1S8fA2A2").
Definition bdAt (j : nat) : list bitem := ltac2:(tb__ "0|0|
S7S11S5dS5eVj;A1S60Vj;A1A2S58Vj;A1A3").
Definition ndAt (j : nat) : ndesc := ltac2:(tb__ "0|0|
S8cSa1Sa0S6aVj;A1S8eSabS3A2A4").

Definition brestAt (j : nat) : list bitem := ltac2:(tb__ "0|0|
S7S11S5dS5eVj;A1S60Vj;A1A2S58ScVj;A1A1A3").
Definition ENDOWs : list bitem := ltac2:(tb__ "0|2|
S0S11S15Z1M0Z0M1S90A3S0S11S15G1G0S8fA3S5S11A1A3A3").

Definition ent_chk2 (L T : axst) (ndi ndj : ndesc) : bool := ltac2:(tb__ "0|3|
S9eS4fS19VL;A1M0S19VT;A1A3S9aS1S1L_;M1S1cVL;VT;R1A3G1S9bR1S4fA2G1Sb7S4fS2cG0A1M2A2G1S93G2Vndi;A2G1Sb1R1S8dVndi;A1S8dVndj;A1A3G1S95R1S94Vndi;A1S94Vndj;A1A3G1Sa6S27G0A1S16R1S92Vndj;A1A2S92Vndi;A1A3S91S8bR1S8aVndj;A1A2S8aVndi;A1A2S4X1x2S4X1x2S4X1x2S4X1x2S4X1x2S4X1x2S4X1x2Ts;").

Definition blk_chk (lastb : bool) (j : nat) (B Bn : axst) (pcn : Z) (d : sv) : bool := ltac2:(tb__ "0|15|
S75VB;A1S18S6dR1Vd;A2S18S5bR1A1S9aS69R2A1SbS25A1M0S5cR3Vd;S47A3S18S5cR4Vd;S48A3S18SadS71R2A1A1M1S18G1S18Sa5R6S46S47R7A4S9aS8cSa1Sa0S74Vj;A1M2S8bR1S8aS4aA1A2A4S89Sa8S1S1R1Lb;S0S1S21S8SfS44A2M3G3G3S99S9SfS44R2A3S9SfS44R1A3A2Lb;La;S4cS1bG3S1bS6SfS44S2eS19S1fR1A1A1A1S1eR1A1A4LL;S9cU12cS5fVB;A3A4S0G3S6SfS44Vpcn;S45A4S0G3S6SfS44SaaS45A4S5G3A1A3A3A4S0S1Sa8S29S3dS2cS19RaA1M4A1M5A1S7S29S0S29S76Vd;A1S5S29A1A3S27G4A1A3A3S0S1SaS18A1S1Lx;M6S84S6eRaVd;A2S7bRaA1A2S18S3La;M7S4Xax2S0S1SaG0A1S1Lx;Sa3R9S46R8A3G0S3Ll;S4Xax2S0S1Sa4R9S46R8R7S4cS8S8S18S89A2M8S2dS2dOF_;F_;M9A2MaS18GaS9S18S89S9G8G9R1A3A3Lp;S68A4A5S0S1Sc6S4fR8A2S0S1Sc4R8Sb0A2S0S1Sb1R8S0S8S28S28A2MbSaeS5GbA1A3S8dS49A1A3S0S1S91S8bR8S8aS49A1A2S8eSabS3A2A2S0S1Sa8S8Sb2G9A2McGcSb4S46Sb0R9G5S9Sb2G9R1A3A5Lp;S68A3S0S1Sb5S72R9Vd;A2S1dR9A1A2S0S1Sb6S7S11S5dS5eVj;A1S60Vj;A1A2S7S11S77R9A1MdS58ScVj;A1MeA1A3MfA3S7S11GdG2A3A2S0S1Sa7S27S19R9A1M10A1S26Z0M11A1G11S58Vj;A1GfA5S0S1S93S2cG10A1M12S61Vj;A1M13A2S0S1S17G12G2A2S0S1Sb7S4fG12A2S0S1G6S84R6S6bR6A1A2G7S4Xax2S0S1G6S84R5S6bR5A1A2G7S4Xax2S0S1S1aR4A1S0S1S1aR3A1S0S1Sa6S27S19R3A1A1S7S11S6aGeA1S6cA3G2A3S0S1S59S5aVB;Vpcn;A2VBn;G13S61GeA1M14A4S0S1S59S5aR4Vpcn;A2VBn;R1G14A4S0S1S1S1Llastb;Vlastb;S3S59S5aR3Vpcn;A2VBn;G14G14A4X1x2S5S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Tndk;Tisk;TTf;TTk;TTf0;TTk0;TR;Ts;TE;TE0;").

Definition blk_dbg (j : nat) (B Bn : axst) (pcn : Z) (d : sv) : list bool := ltac2:(tb__ "0|b|
S75VB;A1S18S6dR1Vd;A2S18S5bR1A1S9aS69R2A1SbS25A1M0S5cR3Vd;S47A3S18S5cR4Vd;S48A3S18SadS71R2A1A1M1S18G1S18Sa5R6S46S47R7A4S9aS8cSa1Sa0S74Vj;A1M2S8bR1S8aS4aA1A2A4S89S0S1SaG0A1S1Lx;Sa3R9S46R8A3G0S3Ll;S4Xax2S0S1Sa4R9S46R8R7S4cS8S8S18S89A2M3S2dS2dOF_;F_;M4A2M5S18G5S9S18S89S9G3G4R1A3A3Lp;S68A4A5S0S1Sb6S7S11S5dS5eVj;A1S60Vj;A1A2S7S11S77R9A1M6S58ScVj;A1M7A1A3M8A3S7S11G6G2A3A2S0S1Sa7S27S19R9A1A1S26Z0M9A1G9S58Vj;A1G8A5S0S1S1aR4A1S0S1S1aR3A1S0S1Sa6S27S19R3A1A1S7S11S6aG7A1S6cA3G2A3S0S1S59S5aVB;Vpcn;A2VBn;S61Vj;A1S61G7A1MaA4S0S1S59S5aR4Vpcn;A2VBn;R1GaA4S0S1S59S5aR3Vpcn;A2VBn;GaGaA4S5S1A1A3A3A3A3A3A3A3A3A3A3Tndk;Tisk;TTf;TTk;TTf0;TTk0;TR;Ts;TE;TE0;").

Lemma epiS2_chk : ltac2:(tb__ "0|0|
S23S22S1S57S4U1S56S62Z8ea64S24P190A1A6S3A3S23S22S1S57S4U2S62S63Z8eae0S24P193A1A6S3A3S23S22S1S57S4U3S63S64Z8eb5cS24P196A1A6S3A3S23S22S1S57S4U4S64S65Z8ebd8S24P199A1A6S3A3S23S22S1S57S4U5S65S66Z8ec54S24P19cA1A6S3A3S22S1S57S3U6S66S67Z8ecd0S24P19fA1A6S3A3A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS2_chk_v0 : ltac2:(tb__ "0|6|
S23S22SbS8SfS44A2M0A1M1S4cS1bG0S1bS6SfS44S2eS19S1fR1A1A1A1S1eR1A1A4LL;M2S7dA4S0G0S6SfS44S79S45A4M3S0G0S6SfS44S78S45A4S0G0G3S5G0A1M4A3A3A3A3S23S22S1S1aS56A1S3A3S23S22S1S1aS62A1S3A3S23S22S1S1aS63A1S3A3S23S22S1S1aS64A1S3A3S23S22S1S1aS65A1S3A3S23S22S1S1aS66A1S3A3S23S22S1S1aS67A1S3A3S23S22S1S1cSa2S73S6fA2S56S9eS4fS19S6fA1S19S56A1M5A3A3S3A3S23S22S1S1cSa2S73S70A2S56S9eS4fS19S70A1G5A3A3S3A3S22G1S4cS1bG0G2S9cU12cS5fS67A3A4S0G0S6SfS44SbbS45A4S0G0S6SfS44Z90850S45A4G4A3A3A3A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
