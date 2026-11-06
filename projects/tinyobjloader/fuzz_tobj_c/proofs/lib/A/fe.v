(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_033.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.

(* [comment removed for export] *)
Module Lib_load_obj_epiS_st1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "app"; "Some"; "prod"; "fst"; "cons"; "list"; "nil"; "option"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.AD"; "Pre_ad"; "nd0"; "P_fail"; "P_ok"; "tv0"; "am_np"; "am_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SVar"; "sprop_eqb"; "ss_facts"; "ss_next"; "SLit"; "SPUle"; "valuation"; "SPBranch"; "SPNot"; "sobj"; "sprop_below"; "SMd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_below"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS_st1"; "E_1"; "E_2"; "E_3"; "R_1"; "R_2"; "R_3"; "E0_1"; "E0_2"; "E0_3"; "Tf0_1"; "Tf0_2"; "Tf0_3"; "Tf_1"; "Tf_2"; "Tf_3"; "Tk0_1"; "Tk0_2"; "Tk0_3"; "Tk_1"; "Tk_2"; "Tk_3"; "TfB_1"; "TfB_2"; "TfB_3"; "TkB_1"; "TkB_2"; "TkB_3"; "qHk_1"; "qHk_2"; "qHk_3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "extraLO"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "kept_ad"; "PDk_ad"; "dupAt"; "xfb_ad"; "B32m"; "ENDOWs"; "Xk_ad"; "bdAt"; "bd_com"; "cAt"; "go_fact"; "kAt"; "s_ad"; "xf_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "AHead"; "am_subst"; "NDA"; "amode"; "nd_below"; "ndesc"; "am_eqb"; "nd_am"; "nd_bd"; "nd_tv"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_epiS_defs"; "ldef_facts"; "nx500"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_epiS_defs.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.

Definition E0_1 : axst := Eval vm_compute in callL B_1.
Definition E_1 : axst := Eval vm_compute in E_ad E0_1 (SVar 400).
Definition R_1 : list sobj := Eval vm_compute in R_ad E_1.
Definition Tk0_1 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_1 (s_ad E_1) R_1 AD.P_ok (Xk_ad E_1 (SVar 400)).
Definition Tf0_1 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_1 (s_ad E_1) R_1 AD.P_fail (Xk_ad E_1 (SVar 400)).
Definition TkB_1 : axst := Eval vm_compute in T_adB Tk0_1.
Definition TfB_1 : axst := Eval vm_compute in T_adB Tf0_1.
Definition Tk_1 : axst := Eval vm_compute in ax_tidy TkB_1.
Definition Tf_1 : axst := Eval vm_compute in ax_tidy TfB_1.
Definition qHk_1 : sv := Eval vm_compute in match am_subst (import_subA (s_ad E_1) AD.Pre_ad AD.P_ok E_1) AD.am_ok with AHead h _ => h | _ => SLit 0 end.
Lemma st_chk_1 : ltac2:(tb__ "0|23|
S1S0S3S65S18S24S1dSeS30A1M0A1A1S4S18S8S18S55S1aP190A1M1A1SaS18A1A3M2S1cG0A1M3A3A3S2A3S1S0S3S64S18S1bS22S21S77S25S78S1aP191A1S1eZ3A1A3M4S1eZ0M5A1M6A3A1A1G3A3S2A3S1S0S3S64S18S1bS1fG4S1aP192A1M7A2A1G3A3S2A3S1S0S3S64S18S1bS1fG7S1eS4fA1A2A1G3A3S2A3S1S0SbSdA1M8S59S80G2S30A2S58S30A1A2S5SdS2aA2A3S1S0S3S74S51S2aG1A2M9S10S2aA1A2S2A3S1S0SbS9S23A1MaA1S6dS2aS11S57S2aA1MbA3S5GaS2dA2A3S1S0S3S6cS2aS11GbS2dS76S6S6SdS5fA2McS20S20OF_;F_;MdA2MeSdGeS7SdS5fS7GcGdR1A3A3Lp;S4cA4A5S2A3S1S0S3S83S66GbA2S2A3S1S0S3S7fGbS6eA2S2A3S1S0S3S84S66S1dSeS2aA1MfA1M10A2S2A3S1S0S3S5eG10S5cS4S6S19S19A2M11S4bS8G11S69SaG11A1A3M12A3S48S4S26S53S54U1M13A1S56G13A1A2M14S4dG13A1M15A3M16S5aS67S2A2M17A4A2S2A3S1S0S3S27G10S4S26G14S4dU2M18A1M19A3M1aA2S2A3S1S0S3S70GbG12S63S12A1A3S2A3S1S0S3S60S5bGbS61S12A1A2G17A2S2A3S1S0S3S75G16G16A2S2A3S1S0S3S75S4S26G14S4S26S28GbS62S12A1A2M1bG19A3M1cA3S4S26G1bG1aA3A2S2A3S1S0S3S29G14A1S2A3S1S0S3S82S1cGfA1M1dG6G5G15G1cA5S2A3S1S0S3S65S6S72GdA2M1eG1eS73S11S6eGbG10S7S72GdR1A3A5Lp;S4cA3S2A3S1S0S3S7aG1dS4bS48S49S2dA5S2A3S1S0S3S7cG1dS4bS48S7bG9A5S2A3S1S0S19S6aGbPdA2G1A3S1S0S19S6aGbP10A2S79Z4G7A2A3S1S0S3S7dG1dA1S2A3S1S0S3S7eS2aA1S2A3S1S0SdS71S11S2aGbS2dS14G9A6S39A3S1S0G8S59S39S4eS39A1A2S5SdS42A2A3S1S0SdS68S42A1S3cA3S1S0S9G11A1M1fS6fS6bGbS11S14S2aA4M20S15A2G12A3S1S0S5dS5bG20S17A2S5aS45S2A2M21A3S1S0SdS71S11S2aGbS2dS13G9A6S33A3S1S0G8S59S33S4eS33A1A2S5SdS3fA2A3S1S0SdS68S3fA1S36A3S1S0G1fS6fS6bGbS11S13S2aA4M22S15A2G12A3S1S0S5dS5bG22S16A2S5aS67ScA2A3S1S0S3SfS3cA1S2A3S1S0S3SfS36A1S2A3S1S0S3S5eS1dSeS3cA1A1S5cS4aS48G1aG21A4A2S2A3S0S3S81S1cSeS36A1A1S4S26S52G18A1S50A3G1aA3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition E0_2 : axst := Eval vm_compute in callL B_2.
Definition E_2 : axst := Eval vm_compute in E_ad E0_2 (SVar 403).
Definition R_2 : list sobj := Eval vm_compute in R_ad E_2.
Definition Tk0_2 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_2 (s_ad E_2) R_2 AD.P_ok (Xk_ad E_2 (SVar 403)).
Definition Tf0_2 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_2 (s_ad E_2) R_2 AD.P_fail (Xk_ad E_2 (SVar 403)).
Definition TkB_2 : axst := Eval vm_compute in T_adB Tk0_2.
Definition TfB_2 : axst := Eval vm_compute in T_adB Tf0_2.
Definition Tk_2 : axst := Eval vm_compute in ax_tidy TkB_2.
Definition Tf_2 : axst := Eval vm_compute in ax_tidy TfB_2.
Definition qHk_2 : sv := Eval vm_compute in match am_subst (import_subA (s_ad E_2) AD.Pre_ad AD.P_ok E_2) AD.am_ok with AHead h _ => h | _ => SLit 0 end.
Lemma st_chk_2 : ltac2:(tb__ "0|23|
S1S0S3S65S18S24S1dSeS31A1M0A1A1S4S18S8S18S55S1aP193A1M1A1SaS18A1A3M2S1cG0A1M3A3A3S2A3S1S0S3S64S18S1bS22S21S77S1aP194A1M4S1eZ0M5A1M6A3A1A1G3A3S2A3S1S0S3S64S18S1bS1fG4S1aP195A1M7A2A1G3A3S2A3S1S0S3S64S18S1bS1fG7S1eS4fA1A2A1G3A3S2A3S1S0SbSdA1M8S59S80G2S31A2S58S31A1A2S5SdS2bA2A3S1S0S3S74S51S2bG1A2M9S10S2bA1A2S2A3S1S0SbS9S23A1MaA1S6dS2bS11S57S2bA1MbA3S5GaS2eA2A3S1S0S3S6cS2bS11GbS2eS76S6S6SdS5fA2McS20S20OF_;F_;MdA2MeSdGeS7SdS5fS7GcGdR1A3A3Lp;S4cA4A5S2A3S1S0S3S83S66GbA2S2A3S1S0S3S7fGbS6eA2S2A3S1S0S3S84S66S1dSeS2bA1MfA1M10A2S2A3S1S0S3S5eG10S5cS4S6S19S19A2M11S4bS8G11S69SaG11A1A3M12A3S48S4S26S53S54U2M13A1S56G13A1A2M14S4dG13A1M15A3M16S5aS67S2A2M17A4A2S2A3S1S0S3S27G10S4S26G14S4dU3M18A1M19A3M1aA2S2A3S1S0S3S70GbG12S63S12A1A3S2A3S1S0S3S60S5bGbS61S12A1A2G17A2S2A3S1S0S3S75G16G16A2S2A3S1S0S3S75S4S26G14S4S26S28GbS62S12A1A2M1bG19A3M1cA3S4S26G1bG1aA3A2S2A3S1S0S3S29G14A1S2A3S1S0S3S82S1cGfA1M1dG6G5G15G1cA5S2A3S1S0S3S65S6S72GdA2M1eG1eS73S11S6eGbG10S7S72GdR1A3A5Lp;S4cA3S2A3S1S0S3S7aG1dS4bS48S49S2eA5S2A3S1S0S3S7cG1dS4bS48S7bG9A5S2A3S1S0S19S6aGbPdA2G1A3S1S0S19S6aGbP10A2S79Z4G7A2A3S1S0S3S7dG1dA1S2A3S1S0S3S7eS2bA1S2A3S1S0SdS71S11S2bGbS2eS14G9A6S3aA3S1S0G8S59S3aS4eS3aA1A2S5SdS43A2A3S1S0SdS68S43A1S3dA3S1S0S9G11A1M1fS6fS6bGbS11S14S2bA4M20S15A2G12A3S1S0S5dS5bG20S17A2S5aS46S2A2M21A3S1S0SdS71S11S2bGbS2eS13G9A6S34A3S1S0G8S59S34S4eS34A1A2S5SdS40A2A3S1S0SdS68S40A1S37A3S1S0G1fS6fS6bGbS11S13S2bA4M22S15A2G12A3S1S0S5dS5bG22S16A2S5aS67ScA2A3S1S0S3SfS3dA1S2A3S1S0S3SfS37A1S2A3S1S0S3S5eS1dSeS3dA1A1S5cS4aS48G1aG21A4A2S2A3S0S3S81S1cSeS37A1A1S4S26S52G18A1S50A3G1aA3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition E0_3 : axst := Eval vm_compute in callL B_3.
Definition E_3 : axst := Eval vm_compute in E_ad E0_3 (SVar 406).
Definition R_3 : list sobj := Eval vm_compute in R_ad E_3.
Definition Tk0_3 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_3 (s_ad E_3) R_3 AD.P_ok (Xk_ad E_3 (SVar 406)).
Definition Tf0_3 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_3 (s_ad E_3) R_3 AD.P_fail (Xk_ad E_3 (SVar 406)).
Definition TkB_3 : axst := Eval vm_compute in T_adB Tk0_3.
Definition TfB_3 : axst := Eval vm_compute in T_adB Tf0_3.
Definition Tk_3 : axst := Eval vm_compute in ax_tidy TkB_3.
Definition Tf_3 : axst := Eval vm_compute in ax_tidy TfB_3.
Definition qHk_3 : sv := Eval vm_compute in match am_subst (import_subA (s_ad E_3) AD.Pre_ad AD.P_ok E_3) AD.am_ok with AHead h _ => h | _ => SLit 0 end.
Lemma st_chk_3 : ltac2:(tb__ "0|23|
S1S0S3S65S18S24S1dSeS32A1M0A1A1S4S18S8S18S55S1aP196A1M1A1SaS18A1A3M2S1cG0A1M3A3A3S2A3S1S0S3S64S18S1bS22S21S77S1aP197A1M4S1eZ0M5A1M6A3A1A1G3A3S2A3S1S0S3S64S18S1bS1fG4S1aP198A1M7A2A1G3A3S2A3S1S0S3S64S18S1bS1fG7S1eS4fA1A2A1G3A3S2A3S1S0SbSdA1M8S59S80G2S32A2S58S32A1A2S5SdS2cA2A3S1S0S3S74S51S2cG1A2M9S10S2cA1A2S2A3S1S0SbS9S23A1MaA1S6dS2cS11S57S2cA1MbA3S5GaS2fA2A3S1S0S3S6cS2cS11GbS2fS76S6S6SdS5fA2McS20S20OF_;F_;MdA2MeSdGeS7SdS5fS7GcGdR1A3A3Lp;S4cA4A5S2A3S1S0S3S83S66GbA2S2A3S1S0S3S7fGbS6eA2S2A3S1S0S3S84S66S1dSeS2cA1MfA1M10A2S2A3S1S0S3S5eG10S5cS4S6S19S19A2M11S4bS8G11S69SaG11A1A3M12A3S48S4S26S53S54U3M13A1S56G13A1A2M14S4dG13A1M15A3M16S5aS67S2A2M17A4A2S2A3S1S0S3S27G10S4S26G14S4dU4M18A1M19A3M1aA2S2A3S1S0S3S70GbG12S63S12A1A3S2A3S1S0S3S60S5bGbS61S12A1A2G17A2S2A3S1S0S3S75G16G16A2S2A3S1S0S3S75S4S26G14S4S26S28GbS62S12A1A2M1bG19A3M1cA3S4S26G1bG1aA3A2S2A3S1S0S3S29G14A1S2A3S1S0S3S82S1cGfA1M1dG6G5G15G1cA5S2A3S1S0S3S65S6S72GdA2M1eG1eS73S11S6eGbG10S7S72GdR1A3A5Lp;S4cA3S2A3S1S0S3S7aG1dS4bS48S49S2fA5S2A3S1S0S3S7cG1dS4bS48S7bG9A5S2A3S1S0S19S6aGbPdA2G1A3S1S0S19S6aGbP10A2S79Z4G7A2A3S1S0S3S7dG1dA1S2A3S1S0S3S7eS2cA1S2A3S1S0SdS71S11S2cGbS2fS14G9A6S3bA3S1S0G8S59S3bS4eS3bA1A2S5SdS44A2A3S1S0SdS68S44A1S3eA3S1S0S9G11A1M1fS6fS6bGbS11S14S2cA4M20S15A2G12A3S1S0S5dS5bG20S17A2S5aS47S2A2M21A3S1S0SdS71S11S2cGbS2fS13G9A6S35A3S1S0G8S59S35S4eS35A1A2S5SdS41A2A3S1S0SdS68S41A1S38A3S1S0G1fS6fS6bGbS11S13S2cA4M22S15A2G12A3S1S0S5dS5bG22S16A2S5aS67ScA2A3S1S0S3SfS3eA1S2A3S1S0S3SfS38A1S2A3S1S0S3S5eS1dSeS3eA1A1S5cS4aS48G1aG21A4A2S2A3S0S3S81S1cSeS38A1A1S4S26S52G18A1S50A3G1aA3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiS_st1.

(* [comment removed for export] *)
Module Lib_load_obj_epiS_st2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "app"; "Some"; "prod"; "fst"; "cons"; "list"; "nil"; "option"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.AD"; "Pre_ad"; "nd0"; "P_fail"; "P_ok"; "tv0"; "am_np"; "am_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SVar"; "sprop_eqb"; "ss_facts"; "ss_next"; "SLit"; "SPUle"; "valuation"; "SPBranch"; "SPNot"; "sobj"; "sprop_below"; "SAlu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_below"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS_st2"; "E_4"; "E_5"; "E_6"; "R_4"; "R_5"; "R_6"; "E0_4"; "E0_5"; "E0_6"; "Tf0_4"; "Tf0_5"; "Tf0_6"; "Tf_4"; "Tf_5"; "Tf_6"; "Tk0_4"; "Tk0_5"; "Tk0_6"; "Tk_4"; "Tk_5"; "Tk_6"; "TfB_4"; "TfB_5"; "TfB_6"; "TkB_4"; "TkB_5"; "TkB_6"; "qHk_4"; "qHk_5"; "qHk_6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "extraLO"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "kept_ad"; "PDk_ad"; "dupAt"; "xfb_ad"; "B32m"; "ENDOWs"; "Xk_ad"; "bdAt"; "bd_com"; "cAt"; "go_fact"; "kAt"; "s_ad"; "xf_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "AHead"; "am_subst"; "NDA"; "amode"; "nd_below"; "ndesc"; "am_eqb"; "nd_am"; "nd_bd"; "nd_tv"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_epiS_defs"; "ldef_facts"; "nx500"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_epiS_defs.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.

Definition E0_4 : axst := Eval vm_compute in callL B_4.
Definition E_4 : axst := Eval vm_compute in E_ad E0_4 (SVar 409).
Definition R_4 : list sobj := Eval vm_compute in R_ad E_4.
Definition Tk0_4 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_4 (s_ad E_4) R_4 AD.P_ok (Xk_ad E_4 (SVar 409)).
Definition Tf0_4 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_4 (s_ad E_4) R_4 AD.P_fail (Xk_ad E_4 (SVar 409)).
Definition TkB_4 : axst := Eval vm_compute in T_adB Tk0_4.
Definition TfB_4 : axst := Eval vm_compute in T_adB Tf0_4.
Definition Tk_4 : axst := Eval vm_compute in ax_tidy TkB_4.
Definition Tf_4 : axst := Eval vm_compute in ax_tidy TfB_4.
Definition qHk_4 : sv := Eval vm_compute in match am_subst (import_subA (s_ad E_4) AD.Pre_ad AD.P_ok E_4) AD.am_ok with AHead h _ => h | _ => SLit 0 end.
Lemma st_chk_4 : ltac2:(tb__ "0|23|
S1S0S3S65S18S24S1dSeS30A1M0A1A1S4S18S8S18S55S1aP199A1M1A1SaS18A1A3M2S1cG0A1M3A3A3S2A3S1S0S3S64S18S1bS22S21S77S25S78S1aP19aA1S1eZ1A1A3M4S1eZ0M5A1M6A3A1A1G3A3S2A3S1S0S3S64S18S1bS1fG4S1aP19bA1M7A2A1G3A3S2A3S1S0S3S64S18S1bS1fG7S1eS4fA1A2A1G3A3S2A3S1S0SbSdA1M8S59S80G2S30A2S58S30A1A2S5SdS2aA2A3S1S0S3S74S51S2aG1A2M9S10S2aA1A2S2A3S1S0SbS9S23A1MaA1S6dS2aS11S57S2aA1MbA3S5GaS2dA2A3S1S0S3S6cS2aS11GbS2dS76S6S6SdS5fA2McS20S20OF_;F_;MdA2MeSdGeS7SdS5fS7GcGdR1A3A3Lp;S4cA4A5S2A3S1S0S3S83S66GbA2S2A3S1S0S3S7fGbS6eA2S2A3S1S0S3S84S66S1dSeS2aA1MfA1M10A2S2A3S1S0S3S5eG10S5cS4S6S19S19A2M11S4bS8G11S69SaG11A1A3M12A3S48S4S26S53S54U4M13A1S56G13A1A2M14S4dG13A1M15A3M16S5aS67S2A2M17A4A2S2A3S1S0S3S27G10S4S26G14S4dU5M18A1M19A3M1aA2S2A3S1S0S3S70GbG12S63S12A1A3S2A3S1S0S3S60S5bGbS61S12A1A2G17A2S2A3S1S0S3S75G16G16A2S2A3S1S0S3S75S4S26G14S4S26S28GbS62S12A1A2M1bG19A3M1cA3S4S26G1bG1aA3A2S2A3S1S0S3S29G14A1S2A3S1S0S3S82S1cGfA1M1dG6G5G15G1cA5S2A3S1S0S3S65S6S72GdA2M1eG1eS73S11S6eGbG10S7S72GdR1A3A5Lp;S4cA3S2A3S1S0S3S7aG1dS4bS48S49S2dA5S2A3S1S0S3S7cG1dS4bS48S7bG9A5S2A3S1S0S19S6aGbPdA2G1A3S1S0S19S6aGbP10A2S79Z4G7A2A3S1S0S3S7dG1dA1S2A3S1S0S3S7eS2aA1S2A3S1S0SdS71S11S2aGbS2dS14G9A6S39A3S1S0G8S59S39S4eS39A1A2S5SdS42A2A3S1S0SdS68S42A1S3cA3S1S0S9G11A1M1fS6fS6bGbS11S14S2aA4M20S15A2G12A3S1S0S5dS5bG20S17A2S5aS45S2A2M21A3S1S0SdS71S11S2aGbS2dS13G9A6S33A3S1S0G8S59S33S4eS33A1A2S5SdS3fA2A3S1S0SdS68S3fA1S36A3S1S0G1fS6fS6bGbS11S13S2aA4M22S15A2G12A3S1S0S5dS5bG22S16A2S5aS67ScA2A3S1S0S3SfS3cA1S2A3S1S0S3SfS36A1S2A3S1S0S3S5eS1dSeS3cA1A1S5cS4aS48G1aG21A4A2S2A3S0S3S81S1cSeS36A1A1S4S26S52G18A1S50A3G1aA3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition E0_5 : axst := Eval vm_compute in callL B_5.
Definition E_5 : axst := Eval vm_compute in E_ad E0_5 (SVar 412).
Definition R_5 : list sobj := Eval vm_compute in R_ad E_5.
Definition Tk0_5 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_5 (s_ad E_5) R_5 AD.P_ok (Xk_ad E_5 (SVar 412)).
Definition Tf0_5 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_5 (s_ad E_5) R_5 AD.P_fail (Xk_ad E_5 (SVar 412)).
Definition TkB_5 : axst := Eval vm_compute in T_adB Tk0_5.
Definition TfB_5 : axst := Eval vm_compute in T_adB Tf0_5.
Definition Tk_5 : axst := Eval vm_compute in ax_tidy TkB_5.
Definition Tf_5 : axst := Eval vm_compute in ax_tidy TfB_5.
Definition qHk_5 : sv := Eval vm_compute in match am_subst (import_subA (s_ad E_5) AD.Pre_ad AD.P_ok E_5) AD.am_ok with AHead h _ => h | _ => SLit 0 end.
Lemma st_chk_5 : ltac2:(tb__ "0|23|
S1S0S3S65S18S24S1dSeS31A1M0A1A1S4S18S8S18S55S1aP19cA1M1A1SaS18A1A3M2S1cG0A1M3A3A3S2A3S1S0S3S64S18S1bS22S21S77S1aP19dA1M4S1eZ0M5A1M6A3A1A1G3A3S2A3S1S0S3S64S18S1bS1fG4S1aP19eA1M7A2A1G3A3S2A3S1S0S3S64S18S1bS1fG7S1eS4fA1A2A1G3A3S2A3S1S0SbSdA1M8S59S80G2S31A2S58S31A1A2S5SdS2bA2A3S1S0S3S74S51S2bG1A2M9S10S2bA1A2S2A3S1S0SbS9S23A1MaA1S6dS2bS11S57S2bA1MbA3S5GaS2eA2A3S1S0S3S6cS2bS11GbS2eS76S6S6SdS5fA2McS20S20OF_;F_;MdA2MeSdGeS7SdS5fS7GcGdR1A3A3Lp;S4cA4A5S2A3S1S0S3S83S66GbA2S2A3S1S0S3S7fGbS6eA2S2A3S1S0S3S84S66S1dSeS2bA1MfA1M10A2S2A3S1S0S3S5eG10S5cS4S6S19S19A2M11S4bS8G11S69SaG11A1A3M12A3S48S4S26S53S54U5M13A1S56G13A1A2M14S4dG13A1M15A3M16S5aS67S2A2M17A4A2S2A3S1S0S3S27G10S4S26G14S4dU6M18A1M19A3M1aA2S2A3S1S0S3S70GbG12S63S12A1A3S2A3S1S0S3S60S5bGbS61S12A1A2G17A2S2A3S1S0S3S75G16G16A2S2A3S1S0S3S75S4S26G14S4S26S28GbS62S12A1A2M1bG19A3M1cA3S4S26G1bG1aA3A2S2A3S1S0S3S29G14A1S2A3S1S0S3S82S1cGfA1M1dG6G5G15G1cA5S2A3S1S0S3S65S6S72GdA2M1eG1eS73S11S6eGbG10S7S72GdR1A3A5Lp;S4cA3S2A3S1S0S3S7aG1dS4bS48S49S2eA5S2A3S1S0S3S7cG1dS4bS48S7bG9A5S2A3S1S0S19S6aGbPdA2G1A3S1S0S19S6aGbP10A2S79Z4G7A2A3S1S0S3S7dG1dA1S2A3S1S0S3S7eS2bA1S2A3S1S0SdS71S11S2bGbS2eS14G9A6S3aA3S1S0G8S59S3aS4eS3aA1A2S5SdS43A2A3S1S0SdS68S43A1S3dA3S1S0S9G11A1M1fS6fS6bGbS11S14S2bA4M20S15A2G12A3S1S0S5dS5bG20S17A2S5aS46S2A2M21A3S1S0SdS71S11S2bGbS2eS13G9A6S34A3S1S0G8S59S34S4eS34A1A2S5SdS40A2A3S1S0SdS68S40A1S37A3S1S0G1fS6fS6bGbS11S13S2bA4M22S15A2G12A3S1S0S5dS5bG22S16A2S5aS67ScA2A3S1S0S3SfS3dA1S2A3S1S0S3SfS37A1S2A3S1S0S3S5eS1dSeS3dA1A1S5cS4aS48G1aG21A4A2S2A3S0S3S81S1cSeS37A1A1S4S26S52G18A1S50A3G1aA3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition E0_6 : axst := Eval vm_compute in callL B_6.
Definition E_6 : axst := Eval vm_compute in E_ad E0_6 (SVar 415).
Definition R_6 : list sobj := Eval vm_compute in R_ad E_6.
Definition Tk0_6 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_6 (s_ad E_6) R_6 AD.P_ok (Xk_ad E_6 (SVar 415)).
Definition Tf0_6 : axst := Eval vm_compute in T_afterA3 AD.Pre_ad E_6 (s_ad E_6) R_6 AD.P_fail (Xk_ad E_6 (SVar 415)).
Definition TkB_6 : axst := Eval vm_compute in T_adB Tk0_6.
Definition TfB_6 : axst := Eval vm_compute in T_adB Tf0_6.
Definition Tk_6 : axst := Eval vm_compute in ax_tidy TkB_6.
Definition Tf_6 : axst := Eval vm_compute in ax_tidy TfB_6.
Definition qHk_6 : sv := Eval vm_compute in match am_subst (import_subA (s_ad E_6) AD.Pre_ad AD.P_ok E_6) AD.am_ok with AHead h _ => h | _ => SLit 0 end.
Lemma st_chk_6 : ltac2:(tb__ "0|23|
S1S0S3S65S18S24S1dSeS32A1M0A1A1S4S18S8S18S55S1aP19fA1M1A1SaS18A1A3M2S1cG0A1M3A3A3S2A3S1S0S3S64S18S1bS22S21S77S1aP1a0A1M4S1eZ0M5A1M6A3A1A1G3A3S2A3S1S0S3S64S18S1bS1fG4S1aP1a1A1M7A2A1G3A3S2A3S1S0S3S64S18S1bS1fG7S1eS4fA1A2A1G3A3S2A3S1S0SbSdA1M8S59S80G2S32A2S58S32A1A2S5SdS2cA2A3S1S0S3S74S51S2cG1A2M9S10S2cA1A2S2A3S1S0SbS9S23A1MaA1S6dS2cS11S57S2cA1MbA3S5GaS2fA2A3S1S0S3S6cS2cS11GbS2fS76S6S6SdS5fA2McS20S20OF_;F_;MdA2MeSdGeS7SdS5fS7GcGdR1A3A3Lp;S4cA4A5S2A3S1S0S3S83S66GbA2S2A3S1S0S3S7fGbS6eA2S2A3S1S0S3S84S66S1dSeS2cA1MfA1M10A2S2A3S1S0S3S5eG10S5cS4S6S19S19A2M11S4bS8G11S69SaG11A1A3M12A3S48S4S26S53S54U6M13A1S56G13A1A2M14S4dG13A1M15A3M16S5aS67S2A2M17A4A2S2A3S1S0S3S27G10S4S26G14S4dU7M18A1M19A3M1aA2S2A3S1S0S3S70GbG12S63S12A1A3S2A3S1S0S3S60S5bGbS61S12A1A2G17A2S2A3S1S0S3S75G16G16A2S2A3S1S0S3S75S4S26G14S4S26S28GbS62S12A1A2M1bG19A3M1cA3S4S26G1bG1aA3A2S2A3S1S0S3S29G14A1S2A3S1S0S3S82S1cGfA1M1dG6G5G15G1cA5S2A3S1S0S3S65S6S72GdA2M1eG1eS73S11S6eGbG10S7S72GdR1A3A5Lp;S4cA3S2A3S1S0S3S7aG1dS4bS48S49S2fA5S2A3S1S0S3S7cG1dS4bS48S7bG9A5S2A3S1S0S19S6aGbPdA2G1A3S1S0S19S6aGbP10A2S79Z4G7A2A3S1S0S3S7dG1dA1S2A3S1S0S3S7eS2cA1S2A3S1S0SdS71S11S2cGbS2fS14G9A6S3bA3S1S0G8S59S3bS4eS3bA1A2S5SdS44A2A3S1S0SdS68S44A1S3eA3S1S0S9G11A1M1fS6fS6bGbS11S14S2cA4M20S15A2G12A3S1S0S5dS5bG20S17A2S5aS47S2A2M21A3S1S0SdS71S11S2cGbS2fS13G9A6S35A3S1S0G8S59S35S4eS35A1A2S5SdS41A2A3S1S0SdS68S41A1S38A3S1S0G1fS6fS6bGbS11S13S2cA4M22S15A2G12A3S1S0S5dS5bG22S16A2S5aS67ScA2A3S1S0S3SfS3eA1S2A3S1S0S3SfS38A1S2A3S1S0S3S5eS1dSeS3eA1A1S5cS4aS48G1aG21A4A2S2A3S0S3S81S1cSeS38A1A1S4S26S52G18A1S50A3G1aA3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiS_st2.

(* [comment removed for export] *)
Module Lib_load_obj_epiS4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "nat"; "app"; "pair"; "nil"; "prod"; "Some"; "false"; "list"; "option"; "fst"; "negb"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_below"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "axwf"; "la_state"; "la_reason"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS4"; "E_ad8"; "E_fu"; "B_8"; "B_9"; "cps_c"; "pc_b9"; "land_chk"; "nd9"; "R_fu"; "T_fu"; "T_fu0"; "Tf8"; "bd9"; "brest8"; "dup8"; "nd8"; "s_fu"; "skipC"; "vSHd"; "B_fu"; "E_fu0"; "Tk8"; "comOf"; "pc_b8"; "L_d6f"; "L_d7"; "L_land"; "Lq_8"; "bd8"; "bd_land"; "callC"; "ekOf"; "iW2"; "nd_d0"; "ndk8"; "xf_fu"; "xfb_fu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "runL"; "leafL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "ss_facts"; "sv"; "SAlu"; "ss_next"; "sobj"; "sprop_below"; "ss_pc"; "valuation"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "ent_chk2"; "bd_com"; "cAt"; "kAt"; "PDk_ad"; "cps_b"; "B_7"; "DUPk"; "DUPv"; "ENDOWs"; "E_adF"; "R_ad"; "Xk_ad"; "bdAt"; "brestAt"; "dupAt"; "go_fact"; "hand_ad"; "iW"; "ndAt"; "s_ad"; "xf_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "AHead"; "NDA"; "nd_below"; "ndesc"; "am_eqb"; "am_subst"; "nd_am"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS4.FU"; "Pre_fu"; "P_fu"; "Posts_fu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "bd_disp"; "pc_disp"; "K_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.AD"; "Pre_ad"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "@Stdlib.Lists.List"; "forallb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.AD.ADAddr"; "ad_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_pay2"; "bud_le2"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1"; "L_dz"; "bd_fz2"; "qHz2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS4.FU.FinUnkAddr"; "fu_entry";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "oidx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.
Definition nd_d0 : ndesc := ndEp tvL bd_disp.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
Module FU. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_finalize_unknowns. End FU.

Definition pc_b8 : Z := 0x8ecec.  Definition pc_b9 : Z := 0x8ee94.
Definition cps_c : list Z := ltac2:(tb__ "0|0|
S3S13S35S3S13S23S60A3A3").
Definition callC (B : axst) : axst := ltac2:(tb__ "0|0|
S4fS4eU12cS22VB;A3S89U0A3").
Definition skipC (B : axst) (pc : Z) : axst := ltac2:(tb__ "0|0|
S4fS4eU12cS22VB;A3Vpc;U0A3").

Definition L_d7 : axst := Eval vm_compute in leafL (runL 300 cps_b B_7) pc_disp 0.
Definition E_fu0 : axst := Eval vm_compute in leafL (runL 300 cps_b B_7) FU.FinUnkAddr.fu_entry 0.
Definition xf_fu (A : axst) : list axform := ltac2:(tb__ "0|2|
S3S44S49S6dVA;A1M0S50Na0M1A1A2S3S44S46G0G1A2S8S44A1A3A3").
Definition E_fu : axst := Eval vm_compute in optL (apply_axforms E_fu0 (xf_fu E_fu0)).
Definition s_fu : wsub := ltac2:(tb__ "0|0|
S3S9S14S53A2S7S14S53P13S54S7eS80S50Za0A1A3A4S9ePaS16S1fA1S16S79A1A3A3").
Definition R_fu : list sobj := Eval vm_compute in optR (entails_frA E_fu FU.Pre_fu s_fu).
Definition T_fu0 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_fu)) (import_postA s_fu FU.Pre_fu FU.P_fu E_fu R_fu).
Definition iW2 (T : axst) : nat := ltac2:(tb__ "0|0|
S9bS54S7eS5aPaA1S50N2a0A1A3S54S7eS80S50Za0A1A3VT;A3").
Definition xfb_fu (T : axst) : list axform := ltac2:(tb__ "0|2|
S3S44S46S3eVT;A1M0Za0A2S3S44S48S3S5G0S3S5U0M1S88S5S5SfS10S94R1G1A2S94R1G0A2A2A1Li;S4cG1S96VT;A1A2A3A3A3A1S3S44S47G1A1S8S44A1A3A3A3").
Definition B_fu : axst := Eval vm_compute in optL (apply_axforms T_fu0 (xfb_fu T_fu0)).
Definition T_fu : axst := Eval vm_compute in ax_tidy B_fu.

Definition Lq_8 : axst := Eval vm_compute in leafL (runL 300 cps_c T_fu) pc_b8 0.
Definition B_8 : axst := Eval vm_compute in nextBj (5%nat :: junk_cs) Lq_8.

Definition junk_9 : list nat := ltac2:(tb__ "0|0|
S3S5U1S3S5U5S3S5U6S3S5U7S3S5UaS3S5UbS3S5UcS3S5UeS3S5UfS3S5U10S3S5U11S3S5U1cS3S5U1dS3S5U1eS3S5U1fS8S5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition B_9 : axst := Eval vm_compute in nextBj junk_9 (skipC B_8 pc_b9).
Definition L_land : axst := Eval vm_compute in leafL (runL 300 cps_c B_9) pc_disp 0.
Definition dup8 : list bitem := ltac2:(tb__ "0|1|
S3S11S63Z0M0G0G0G0Z60A5S3S11S62G0G0G0G0Z40A5S8S11A1A3A3").
Definition bd8 : list bitem := bdAt 7.
Definition brest8 : list bitem := ltac2:(tb__ "0|1|
S6S11S5cS5dU7M0A1S5eG0A1A2S2cA3").
Definition bd9 : list bitem := ltac2:(tb__ "0|1|
S6S11S5cS5dU8M0A1S5eG0A1A2S2cA3").
Definition nd8 : ndesc := ltac2:(tb__ "0|0|
S72S7dS7cS3aS71S43S4A2A4").
Definition nd9 : ndesc := ltac2:(tb__ "0|0|
S72S7dS7cS2aS71S43S4A2A4").
Definition vSHd : sv := SVar 418.
Definition E_ad8 : axst := Eval vm_compute in E_ad (callC B_8) vSHd.
Definition Tk8 : axst := Eval vm_compute in ax_tidy (T_adB (T_ad0 E_ad8 vSHd AD.P_ok)).
Definition Tf8 : axst := Eval vm_compute in ax_tidy (T_adB (T_ad0 E_ad8 vSHd AD.P_fail)).
Definition ndk8 : ndesc := Eval vm_compute in NDA tvL frL brest8 (am_subst (import_subA (s_ad E_ad8) AD.Pre_ad AD.P_ok E_ad8) (nd_am AD.ndK)).

Lemma epiS4_chk_fu : ltac2:(tb__ "0|b|
S1S0ScS9S13S1cA2M0A1M1S4aS17G0S17S7S13S1cS58S16S19R1A1A1A1S1aR1A1A4LL;M2S4eU12cM3S60S61A3A4S3G0S7S13S1cS82S1dA4S3G0S7S13S1cS9aS1dA4S8G0A1M4A3A3A3S1S0SdS15A1M5S45S32S41S32A1A2SaS15S1fA2A3S1S0SdScS56A1M6A1S8aS1fS79S2eA3SaG6S26A2A3S1S0S2S8bS1fS79S2eS26S4aS17S15S19S7bA4A5S4A3S1S0S2S95S7fS55S16S1fA1M7A1M8A2S4A3S1S0S2S73G8S6eU7A1M9A2S4A3S1S0S2S87S51S57G8A1S52G7A1MaA3S4A3S1S0S15Sa0GaS8dS2eS79S7aS1fS26A5A2S28A3S1S0G5S45S28S42S28A1A2SaS15S31A2A3S1S0S15S9cS31A1S27A3S1S0S2S18S27A1S4A3S1S0G1S4aS17G0G2S4eG3S22S27A3A4S3G0S7S13S1cS35S1dA4G4A3A3S1S0S2S18S20A1S4A3S0S2S5bS39S20G9S2dA4S4A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS4_chk_sh : ltac2:(tb__ "0|15|
S1S0ScS9S13S1cA2M0A1M1S4aS17G0S17S7S13S1cS58S16S19R1A1A1A1S1aR1A1A4LL;M2S4eU12cM3S22S20A3A4S3G0S7S13S1cS23S1dA4S3G0S7S13S1cS89S1dA4S8G0A1M4A3A3A3S1S0S2S87S51S57S55S16S3cS20A1M5A1M6A1A1S6S51S3S51S6bS30A1S8S51A1A3S52G6A1A3A3S4A3S1S0SdS15A1S45S65G5S30A2S70G5A1A2SaS15S1eA2A3S1S0SdScS56A1M7A1S8aS1eS84S6fS1eA1M8A3SaG7S66S1eA1M9A2A3S1S0S2S8cS1eS84G8G9S4aS9S9S15S74A2MaS59S59OF_;F_;MbA2McS15GcSeS15S74SeGaGbR1A3A3Lp;S5fA4A5S4A3S1S0S2Sa2S7fG8A2S4A3S1S0S2S9fG8S8eA2S4A3S1S0S2Sa1G8S3S9S53S53A2MdS9dS8GdA1A3S78S85A1A3S4A3S1S0S2S75S76G8S77S85A1A2S71S43S4A2A2S4A3S1S0S2S87S9S8fGbA2MeGeS90S84S8eG8S55S16S1eA1MfA1M10SeS8fGbR1A3A5Lp;S5fA3S4A3S1S0S2S91S67S1eS30A2S1bS1eA1A2S4A3S1S0S2S86S6S11S5cS5dU7M11A1S5eG11A1A2S6S11S6cS1eA1M12S2cA3M13A3S6S11G12S2bA3A2S4A3S1S0S2S92S52GfA1S50Z0M14A1G14S6aG11A1G13A5S4A3S1S0S2S73G10S2dA2S4A3S1S0S2S12G10S2bA2S4A3S1S0S2S95S7fG10A2S4A3S1S0S2S18S33A1S4A3S1S0S2S18S29A1S4A3S1S0S2S93S52S16S29A1A1S6S11S2aS64A3S2bA3S4A3S1S0S2S18S21A1S4A3S1S0S2S5bS2fS20S23A2S21S2dS25A4S4A3S1S0S2S5bS2fS33S23A2S21S40S25A4S4A3S1S0S2S5bS2fS29S23A2S21S25S25A4S4A3S0G1S4aS17G0G2S4eG3S22S21A3A4S3G0S7S13S1cS82S1dA4G4A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition ndP (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S72S7dS7cVbd;S71S43SbA2A4").
Definition E_ad6 : axst := Eval vm_compute in E_ad (callL B_6) (SVar 415).
Definition Tf6 : axst := Eval vm_compute in ax_tidy (T_adB (T_ad0 E_ad6 (SVar 415) AD.P_fail)).
Definition L_d6f : axst := Eval vm_compute in leafL (runL 300 cps_b Tf6) pc_disp 0.

Definition ekOf (bd : list bitem) : list bitem := firstn 1 (skipn 1 bd).
Definition comOf (bd : list bitem) : list bitem := ltac2:(tb__ "0|0|
S6S11S4bS11U1Vbd;A3S4dS11U2Vbd;A3A3").
Definition bd_land (bd : list bitem) : list bitem := ltac2:(tb__ "0|0|
S6S11S81S34Vbd;A1A3").
Definition land_chk (L : axst) (bd : list bitem) (hd : sv) : bool := ltac2:(tb__ "0|5|
S2S2L_;M0S86Vbd;S6S11S34Vbd;A1M1S3dVbd;A1M2A3A2G0S86S6S11G1S81A3S3bVbd;A1M3A2G0S92S52S16VL;A1A1S50Z0M4A1G4G2S81A5S5bVL;S83S72S7dS7cG3S71Vhd;SbA2A4S3fA4SbX2x2SbX2x2SbX2x2").
Lemma epiS4_chk_land : ltac2:(tb__ "0|0|
S1S0S2S24S38S2aS43A3S4A3S1S0S2S24S37S68U7A1S43A3S4A3S1S0S2S24S36S69U6A1S43A3S4A3S0S2S24S97S98S99A3S4A3A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiS4.

(* [comment removed for export] *)
Module Lib_load_obj_epiCF.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "prod"; "bool"; "true"; "app"; "nat"; "andb"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sv"; "SPUle"; "SMd"; "SAlu"; "cell"; "sobj"; "sv_eqb"; "SPBranch"; "SVar"; "ss_objs"; "ss_pc"; "SPNot"; "SPUlt"; "c_off"; "c_width"; "mkCell"; "mkObj"; "mkSS"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "apply_axforms"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "ALU_ADD"; "ALU_SUB"; "BC_GEU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_reason"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "vNV"; "fact_nv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "AHead"; "NDA"; "ND"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiCF"; "cbI"; "Nt"; "Wt"; "k_ac"; "tv_vr"; "vI"; "PD_vr"; "bd_grown"; "bd_vr"; "brest_vr"; "cntI"; "d_ac"; "kept_vr"; "nv_pos"; "tv_grown"; "vDg"; "vKg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "bA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "list_set"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "optL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiCF.VRN"; "B32"; "B_EW"; "P_fail"; "P_grown"; "P_keep"; "bdP"; "nd0"; "tv0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "B32m"; "iW"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "oidx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "liftPD"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
Module VRN. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN. End VRN.

Definition vr_pc : Z := 0x9311c.
Definition vI : sv := SVar 680.
Definition cntI : sv := SMd M_MUL (SLit 3) vI.
Definition Wt : sv := SAlu ALU_ADD cntI (SLit 3).
Definition Nt : sv := ltac2:(tb__ "0|0|
SfS31SeS30SaZ3A1S3bA3SaZ2A1A3").
Definition cbI : sv := SMd M_MUL cntI (SLit 4).
Definition d_ac : sv := SVar 415.  Definition k_ac : sv := SVar 417.

Definition vcf (k : Z) : sv := ltac2:(tb__ "0|0|
SfS31SeS30SaZ4A1SfS32S3bS4aA3A3SaVk;A1A3").

Definition set_reg_next (A : axst) (r : nat) (v : sv) (nx : positive) : axst := ltac2:(tb__ "0|0|
S36VA;A1S29S38VA;S1dS16R1A1S5aScS27R1A1Vr;Vv;A4S25R1A1S24R1A1S28R1A1S15R1A1S23R1A1Vnx;S26R1A1A9A2TS;").
Definition set_cnt (A : axst) (c : sv) : axst := ltac2:(tb__ "0|3|
S6cVA;S41S11S11S11S4S11L_;S8S12S1eR1A1M0S58A2S12S22R1A1M1SaZ118A1A2A2S1cG0G1S21R1A1S41S10S10S10S4S10L_;S12S19R1A1M2SaZ120A1A2S1bG2S1aR1A1Vc;A3R1X4x2Lcl;S1fR1A1A4S20R1A1A5R1X4x2Lo;S15S36VA;A1A1A4A2").

Definition nv_pos : sprop := SPUlt (SLit 0) vNV.
Definition nv_src : sprop := ltac2:(tb__ "0|1|
S13S33SeS30S3bSaZ3A1M0A3G0A3").
Definition ent_facts : list sprop := ltac2:(tb__ "0|0|
S0SbS3cS0SbS52S1SbA1A3A3").
Definition L_cfE : axst := Eval vm_compute in ax_add_facts ent_facts L_cf0.
Definition inv_cf : list sprop := ltac2:(tb__ "0|0|
S0SbS18S4aS3bA2S0SbSdS4fS48A2S1SbA1A3A3").
Definition C_cf : axst := Eval vm_compute in junkR [1; 11; 12]%nat (ax_add_facts inv_cf (dropV [416]%positive (set_cnt (set_reg_next L_cfE 20 vI 681) cntI))).

Definition cnt0_src : sprop := ltac2:(tb__ "0|0|
S17S13S34S14P1a0A1SaZ0A1A3A1").
Definition L_cfZ : axst := Eval vm_compute in set_cnt L_cfE (SLit 0).
Definition s_ent : wsub := Eval vm_compute in infer_sub NP (ax_S L_cfZ) (ax_S C_cf).

Definition Ls_c : list leafA := Eval vm_compute in runL 300 cps_b C_cf.
Definition E_c0 : axst := Eval vm_compute in leafL Ls_c vr_pc 0.
Definition xf_vr (T : axst) : list axform := ltac2:(tb__ "0|4|
S0S2aS2eS6bVT;A1M0SaN40M1A1A2S0S2aS2bG0G1A2S1S2aA1M2A3A3S9S2aA1S5dS2fVT;R1A2A1S35S6S2aR2S0S2aS2bS6dS58SaZ118M3A1R1A3G3A2G2A3A3TT1;Tpre;").
Definition room_vr : list sprop := ltac2:(tb__ "0|2|
S0SbSdSeS30SaZ4A1M0S47A3M1SeS30G0S46A3A2S0SbSdG1SaS5fA1A2S0SbSdS47S46A2S1SbA1A3A3A3").
Definition E_c1 : axst := Eval vm_compute in optL (apply_axforms E_c0 (xf_vr E_c0)).
Definition E_c : axst := Eval vm_compute in ax_add_facts room_vr E_c1.
Definition s_c : wsub := Eval vm_compute in (h0, pH) :: (19%positive, SAlu ALU_ADD vDp (SLit 64)) :: (59%positive, Nt) :: infer_sub 10 (ax_S E_c) (ax_S VRN.Pre_vr).
Definition R_c : list sobj := Eval vm_compute in optR (entails_frA E_c VRN.Pre_vr s_c).
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S3S35S3dA2M0S2S35S3dS62S64A4S0G0S2S35S3dS60S40S65S1S3S3ScS43A2ScA2A1M1S1S6eA1A3A4S0G0S2S35S3dS61S40S66G1S63S68S67A2A3A4S1G0A1A3A3A3").
Definition PDk_vr : list pdescK := ltac2:(tb__ "0|0|
S70S6fS4bS5cS5A3A1").

Definition passed_vr : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3ScScA2M0S2ScScS50S44Z4S48A2A4S1G0A1A3").
Definition kept_vr : list (sv * sv) := Eval vm_compute in List.filter (fun t => negb (sv_eqb (fst t) d_ac)) tvL.
Definition tv_vr : list (sv * sv) := kept_vr ++ passed_vr.
Definition bd_cf : list bitem := Eval vm_compute in nd_bd nd_succ.
Definition hand_vr : list bitem := Eval vm_compute in bd_subst s_c (nd_bd (ndh h0 true VRN.nd0)).
Definition brest_vr : list bitem := Eval vm_compute in (firstn 12 bd_cf ++ skipn 14 bd_cf).
Definition bd_vr : list bitem := hand_vr ++ brest_vr.
Definition Xk_vr : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_ac)) (ax_X E_c).
Definition nd_cf : ndesc := ltac2:(tb__ "0|0|
S3fS49S56S4dS3eS57S5A2A4").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S3fS49S56S4eS3eS57S5A2A4").

Definition T_keep0 : axst := Eval vm_compute in T_afterA3 VRN.Pre_vr E_c s_c R_c VRN.P_keep Xk_vr.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 VRN.Pre_vr E_c s_c R_c VRN.P_grown Xk_vr.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 VRN.Pre_vr E_c s_c R_c VRN.P_fail Xk_vr.
Definition isub_grown : wsub := Eval vm_compute in import_subA s_c VRN.Pre_vr VRN.P_grown E_c.
Definition vDg : sv := Eval vm_compute in sv_subst isub_grown VRN.vDn.
Definition vKg : sv := Eval vm_compute in sv_subst isub_grown VRN.vKn.
Definition tv_grown : list (sv * sv) := ltac2:(tb__ "0|1|
S6S3ScScA2M0S51S0G0S2ScScS54S44Z4S55A2A4S1G0A1A3A3").
Definition bd_grown : list bitem := Eval vm_compute in (bd_subst isub_grown (VRN.bdP VRN.vN VRN.vKn) ++ brest_vr).
Definition nd_grown : ndesc := ltac2:(tb__ "0|0|
S3fS53S56S4cS3eS57S5A2A4").

Definition xfb_vr (T : axst) : list axform := ltac2:(tb__ "0|3|
S0S2aS2bU1M0Z40A2S0S2aS2bU2M1N118A2S0S2aS2dS0S7G0S0S7U0M2S42G1S5bS69VT;A1G1A2A2A3A3A1S0S2aS2cG2A1S1S2aA1A3A3A3A3").
Definition B_keep : axst := Eval vm_compute in optL (apply_axforms T_keep0 (xfb_vr T_keep0)).
Definition B_grown : axst := Eval vm_compute in optL (apply_axforms T_grown0 (xfb_vr T_grown0)).
Definition B_fail : axst := Eval vm_compute in optL (apply_axforms T_fail0 (xfb_vr T_fail0)).
Definition T_keep : axst := Eval vm_compute in ax_tidy B_keep.
Definition T_grown : axst := Eval vm_compute in ax_tidy B_grown.
Definition T_fail : axst := Eval vm_compute in ax_tidy B_fail.

Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|1|
S0SbSdSfS31S45SaZcA1A3S44Z4Vk;A2M0A2S0SbSdS45G0A2S0SbSdS45SaS5eA1A2S1SbA1A3A3A3").
Definition T_keepS : axst := Eval vm_compute in ax_add_facts (slot_facts k_ac) T_keep.
Definition T_grownS : axst := Eval vm_compute in ax_add_facts (slot_facts vKg) T_grown.
Definition K_w : axst := T_keepS.
Definition s_gk : wsub := Eval vm_compute in infer_sub NP (ax_S T_grownS) (ax_S K_w).

Definition Ls_w : list leafA := Eval vm_compute in runL 400 cps_b K_w.
Definition L_bk : axst := Eval vm_compute in leafL Ls_w pc_cf 0.
Definition L_x : axst := Eval vm_compute in leafL Ls_w pc_vf0 0.
Definition Ls_f : list leafA := Eval vm_compute in runL 300 cps_b T_fail.
Definition Lf0 : axst := Eval vm_compute in leafL Ls_f pc_disp 0.
Definition Lf1 : axst := Eval vm_compute in leafL Ls_f pc_disp 1.
Definition s_bk : wsub := Eval vm_compute in infer_sub NP (ax_S L_bk) (ax_S C_cf).

Definition bnd_nt : sprop := ltac2:(tb__ "0|0|
SdS14P19aA1SaS6aA1A2").
Definition L_xF : axst := Eval vm_compute in ax_add_facts [bnd_nt] L_x.

Definition pcsOf (Ls : list leafA) : list (Z * stop_reason) := ltac2:(tb__ "0|0|
S41S37S3S43S59A2S37S2S43S59S16S36S3aR1A1A1A1S39R1A1A4LL;VLs;A4").

End Lib_load_obj_epiCF.

