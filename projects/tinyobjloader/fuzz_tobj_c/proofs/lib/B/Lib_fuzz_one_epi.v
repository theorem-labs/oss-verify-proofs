(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "bool"; "true"; "nil"; "Some"; "prod"; "list"; "option"; "pair"; "app"; "fst"; "negb"; "orb"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "has_facts"; "ax_setS"; "axwf"; "entailsA"; "g8"; "ax_X"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "sv"; "sprop"; "ss_objs"; "DUnknown"; "SVar"; "mkObj"; "obj_wf"; "SPEq"; "SPUle"; "cell"; "sv_eqb"; "swf"; "DZero"; "SAlu"; "ob_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_epi"; "K_sx"; "K_sx2"; "X_u1"; "X_u3"; "C_epi"; "X_fin"; "X_rl1"; "C_rl"; "K_sx3"; "K_sx1"; "X_sx2"; "X_u2"; "X_u4"; "cfg_mid"; "s_fin"; "s_sxE"; "s_sxK"; "X_ret"; "X_rl"; "X_sx"; "sel_rel"; "xf_sx"; "xf_un1"; "xf_un2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one"; "gF"; "Fx"; "nx"; "vF"; "oBack"; "pFL"; "runF"; "showL"; "body_shape"; "cfg_obj"; "glob_shape"; "oH"; "pF"; "pc_rel"; "shapes"; "vCFG"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@Stdlib.Lists.List"; "nth_error"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "O_W_fz"; "fz_facts"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2"; "P_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_ad"; "L_sxE"; "L_sxK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_glue"; "vDN"; "vH"; "al_facts"; "vG10"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "nth"; "skipn"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.FZAddr"; "fz_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one.LD"; "cfg_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "flag_carve_stateA"; "release_objs_ok"; "shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_fuzz_iface2 Lib_fuzz_one_glue Lib_fuzz_one Lib_fuzz_one_ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import FZAddr.

Definition K_sx : axst := Eval vm_compute in upd_obj_at (upd_obj_at (keep_below 144 (junkRN [1; 11; 12; 13; 14]%nat L_sxK)) 1 nocells_obj) 0 nocells_obj.
Definition s_sxE : wsub := ltac2:(tb__ "0|0|
S5cS47S16S65A1S16S2fA1A3").
Definition s_sxK : wsub := ltac2:(tb__ "0|0|
S5cS47S16S66A1S16S2fA1A3").

Definition cfg_mid : sobj := ltac2:(tb__ "0|0|
S25S4bS1fZ20A1S1fZb0A1S4S29A1S23A5").
Definition xf_sx : list axform := ltac2:(tb__ "0|2|
S0S10S12S0S1U0S0S1U1S0S1U2S0S1U3S0S1U4S0S1U6S0S1U5M0S0S1U7S0S1U8S0S1U9S0S1UaS4S1A1A3A3A3A3A3A3A3A3A3A3A3A1S0S10S13G0A1M1S0S10G1S4S10A1A3A3A3").
Definition X_sx (A : axst) : list (sv * sv) := ltac2:(tb__ "0|2|
S60S6S20S20A2M0G0ScSdS2aSbS20S20R1A3M1S4bA2S2aG1S57A2A2A1Lr;S1cVA;A1A3").
Definition K_sx1 : axst := Eval vm_compute in ax_setS K_sx (reshape_obj_at (ax_S K_sx) 5 cfg_mid).
Definition K_sx2 : axst := Eval vm_compute in optL (apply_axforms K_sx1 xf_sx).
Definition X_sx2 : list (sv * sv) := Eval vm_compute in X_sx K_sx2.
Definition K_sx3 : axst := Eval vm_compute in shadow_reopen_stateA K_sx2 X_sx2 gF 0 32.
Definition C_epi : axst := Eval vm_compute in flag_carve_stateA K_sx3 pFL.

Definition X_rl : axst := Eval vm_compute in leafF (runF C_epi) pc_rel 0.

Definition sel_rel : list nat := ltac2:(tb__ "0|0|
S0S1U0S0S1U1S0S1U2S0S1U3S0S1U4S0S1U7S0S1U8S0S1U5S0S1U6S0S1U9S0S1UaS4S1A1A3A3A3A3A3A3A3A3A3A3A3").
Definition X_rl1 : axst := Eval vm_compute in optL (apply_axforms X_rl [AXSelect sel_rel]).
Definition C_rl : axst := Eval vm_compute in ax_setS X_rl1 (set_objs (ax_S X_rl1) (firstn 7 (ss_objs (ax_S X_rl1)))).
Definition X_ret : axst := Eval vm_compute in leafF (runF C_rl) fz_ret 0.

Definition xf_un1 : list axform := ltac2:(tb__ "0|2|
S0S10S12S0S1U2S0S1U0M0S0S1U1S0S1U3S0S1U4S0S1U5S0S1U6S4S1A1A3A3A3A3A3A3A3A1S0S10S13G0A1M1S0S10G1S4S10A1A3A3A3").
Definition X_u1 : axst := Eval vm_compute in optL (apply_axforms X_ret xf_un1).
Definition X_u2 : axst := Eval vm_compute in ax_setS X_u1 (reshape_obj_at (ax_S X_u1) 0 oBack).
Definition xf_un2 : list axform := ltac2:(tb__ "0|1|
S0S10S13U0M0A1S0S10S14G0S1fN120A1A2S4S10A1A3A3").
Definition X_u3 : axst := Eval vm_compute in optL (apply_axforms X_u2 xf_un2).
Definition X_u4 : axst := Eval vm_compute in ax_setS X_u3 (reshape_obj_at (ax_S X_u3) 0 O_W_fz).
Definition X_fin : axst := Eval vm_compute in optL (apply_axforms X_u4 [AXSelect [1;0;2;3;4]%nat]).
Definition s_fin : wsub := ltac2:(tb__ "0|0|
S5cS47S16S34A1S16S64A1A3").

Lemma fz_checks_sx : ltac2:(tb__ "0|5|
SfSeS2S19S2fA1S3A3SfSeS2S1aS65S2fS3eA3S3A3SfSeS2S1aS66S2fS3fA3S3A3SfSeS2S5dS3eS47A2S3A3SfSeS2S5dS3fS47A2S3A3SfSeS7S6S6S20S20A2M0S20A2M1A1S56S2fA1SaG1S50S52A3A3SfSeS8S1eA1S5fS1eS22S16S2fA1M2A1U5M3A3S5S1eS51S72S2cA2A2A3SfSeS2S26S4aS2fA1S3cA2S3A3SfSeS15S18S2fS5eG2G3S3cA3A2S38A3SfSeS8S15A1S11S38S44A2S5S15S30A2A3SfSeS7G0A1S42S30A1S39A3SfSeS20S1dS30A1S1fS76A1A3SfSeS2S17S0S21S27S1bS48A1S4bA2S0S21S28S24S48A1S1fS6cS6bZ2Z3dA2Z1A2A1A2S4S21A1A3A3S49S30A1A2S3A3SfSeS15S75S30S39S48Z0Z20A5S37A3SfSeS2S2bS16S37A1A1S3A3SfSeS15S73S37S4dA2S33A3SfSeS2S2bS16S33A1A1S3A3SfSeS2S19S33A1S3A3SeS7S6S58S59A2M4A1S4fS4eS33A1A1S0G4S9S58S59S55S5aA4S4G4A1A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_checks_rl : ltac2:(tb__ "0|e|
SfSeS8S15A1M0S11S41S0S10S12S43A1S4S10A1M1A3A2S5S15S35A2A3SfSeS15S18S35S5bS16S35A1M2S6dS1eU7M3S22G2A1M4A3A2A2S36A3SfSeS2S74S54S4dS48Z2M5S6fS1eG3G4A3A5S3A3SfSeS2S17S0S21S27S1bS48A1S4bA2S0S21S28S24S48A1S1fS6cS6bG5Z3dA2Z1A2A1A2S4S21A1A3A3S49S35A1A2S3A3SfSeS2S19S36A1S3A3SfSeS7S6S58S59A2M6A1S4fS4eS36A1A1S0G6S9S58S59S71S5aA4S4G6A1A3A3SfSeG0S11S40S45A2S5S15S31A2A3SfSeS8S1eA1M7S5fS1eS22S16S31A1M8A1M9U0MaA3S5S1eS25S68S67S1fZe0A1S2eS6eS1eGaG9S53A4A1S23A5A2A3SfSeS2S26S4aS31A1S4cA2S3A3SfSeS2S17S62S49S31A1MbA2S3A3SfSeS2S17S69S68S67S6aA3GbA2S3A3SfSeS15S18S31S5eG8GaS4cA3A2S3aA3SfSeG0S11S3aS46A2S5S15S32A2A3SfSeG7S5fS1eS22S16S32A1McA1GaA3S5S1eS25S24PaA1S2dS70S63S1fN120A1MdA3GdS4S29A1S23A5A2A3SfSeS2S26S4aS32A1S61A2S3A3SfSeS2S17S62S49S32A1A2S3A3SfSeS15S18S32S5eGcGaS61A3A2S3bA3SfSeG0S11S3bS0S10S12S0S1U1S0S1GaS0S1U2S0S1U3S0S1U4S4S1A1A3A3A3A3A3A1G1A3A2S5S15S34A2A3SfSeS2S1aS34S64S3dA3S3A3SfSeS2S5dS3dS47A2S3A3SeS2S77S47S4aS34A1A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
