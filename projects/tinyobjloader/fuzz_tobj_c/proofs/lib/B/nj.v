(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni DrvFw.

(* [comment removed for export] *)
Module FpsD_st.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "sym_runA"; "la_state"; "mkLeafA"; "ax_setS"; "axwf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "Some"; "option"; "list"; "false"; "cons"; "nil"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sprop"; "ss_lenient"; "SVar"; "sstate"; "SPEq"; "sobj"; "ss_facts"; "sv"; "SLit"; "sprop_eqb"; "ss_pc"; "swf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsD_st"; "E4S"; "Pre"; "E2"; "E6bS"; "E6sS"; "s_isl"; "E1"; "E4"; "T3"; "T7b"; "T7s"; "s_sib"; "s_sis"; "E6b"; "E6s"; "R_isl"; "R_rip"; "R_sib"; "R_sis"; "T3B"; "T3S"; "T5"; "T5F"; "s_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "CUTS_FPS"; "facts_fps"; "FSB"; "FSS"; "fs_ok"; "runp"; "zvar"; "XF6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st"; "Pre_si"; "P_si"; "Posts_si"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen"; "Pre_isl"; "P_isl"; "Posts_isl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.Lists.List"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsB"; "factsS"; "sX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates"; "obindW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen.ISLAddr"; "isl_entry"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition Pre : axst := Pre_fps FMT_RDERR 0x1ee40 0x80.

Definition run1__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S3aU7d0S3bS23SbA5").
Local Strategy expand [run1__R].
Definition E1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => lf0 Pre (ro1__) 0) run1__R).
Definition run2__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S3aUbb8S3bS28SbA5").
Local Strategy expand [run2__R].
Definition E2 := Eval vm_compute in ((fun ro2__ : option (list leafA) => lf0 E1 (ro2__) 0) run2__R).
Definition s_isl := Eval vm_compute in ((16%positive, SVar 16) :: infer_sub 10 (ax_S E2) (ax_S Pre_isl)).
Definition R_isl := Eval vm_compute in match entails_frA E2 Pre_isl s_isl with Some R => R | None => [] end.
Definition T3 := Eval vm_compute in import_postA s_isl Pre_isl P_isl E2 R_isl.

Definition T3S : axst := ltac2:(tb__ "0|0|
S52S12S14S56S3cA3S2aA2").
Definition E6s := Eval vm_compute in match runp FSS T3S with Some A => A | None => T3S end.
Definition E6sS := Eval vm_compute in match apply_axforms E6s [AXSplit 1 (SLit (-1024))] with Some A => A | None => E6s end.
Definition s_sis := Eval vm_compute in ([(16%positive, SVar 16); (17%positive, SVar 17); (20%positive, SVar 20)] ++ infer_sub 10 (ax_S E6sS) (ax_S Pre_si)).
Definition R_sis := Eval vm_compute in match entails_frA E6sS Pre_si s_sis with Some R => R | None => [] end.
Definition T7s := Eval vm_compute in import_postA s_sis Pre_si P_si E6sS R_sis.

Definition T3B : axst := ltac2:(tb__ "0|0|
S52S12S14S55S3cA3S2aA2").
Definition run3b__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S3aUbb8S3bS35SbA5").
Local Strategy expand [run3b__R].
Definition E4 := Eval vm_compute in ((fun ro3__ : option (list leafA) => lf0 T3B (ro3__) 0) run3b__R).
Definition E4S := Eval vm_compute in
  match split_obj_at (ax_S E4) 1 (SLit (-2352)) with Some S1 =>
  match split_obj_at S1 1 (SLit (-2432)) with Some S2 => ax_setS E4 S2 | None => E4 end | None => E4 end.
Definition s_rip := Eval vm_compute in ((16%positive, vXL8) :: infer_sub 10 (ax_S E4S) (ax_S Pre_rip)).
Definition R_rip := Eval vm_compute in match entails_frA E4S Pre_rip s_rip with Some R => R | None => [] end.
Definition T5 := Eval vm_compute in import_postA s_rip Pre_rip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.P_ret E4S R_rip.
Definition T5F : axst := ltac2:(tb__ "0|0|
S52S10S14S18S16P8cA1S16P10A1A2S12S14S55S3cA3A3S37A2").
Definition E6b := Eval vm_compute in match runp FSB T5F with Some A => A | None => T5F end.
Definition E6bS := Eval vm_compute in match apply_axforms E6b XF6 with Some A => A | None => E6b end.
Definition s_sib := Eval vm_compute in ([(16%positive, SVar 16); (17%positive, SVar 17); (20%positive, SVar 20)] ++ infer_sub 10 (ax_S E6bS) (ax_S Pre_si)).
Definition R_sib := Eval vm_compute in match entails_frA E6bS Pre_si s_sib with Some R => R | None => [] end.
Definition T7b := Eval vm_compute in import_postA s_sib Pre_si P_si E6bS R_sib.

Lemma pre_wf : ltac2:(tb__ "0|0|
S1S0SaS9S23A1SbA3S0SaS1fS2S23A1A1SbA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pre_facts : ltac2:(tb__ "0|0|
S0SeS14A1S1aS2S23A1A1S3cA3"). Proof. reflexivity. Qed.
Lemma xs4 : ltac2:(tb__ "0|0|
S0S3S8S29S2S22A1A2S22A3"). Proof. reflexivity. Qed.
Lemma lenT7 : ltac2:(tb__ "0|0|
S1S0SaS15S2S2cA1A1SfA3S0SaS15S2S2bA1A1SfA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma run1 : ltac2:(tb__ "0|1|
S0SdSeS4A1M0A1S5S3aU7d0S3bS23SbA5ScG0S10S4S7S28S51A2S11S4A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run1__R <: run1__R = Some [mkLeafA E1 RsCut]). Qed.
Lemma run2 : ltac2:(tb__ "0|1|
S0SdSeS4A1M0A1S5S3aUbb8S3bS28SbA5ScG0S10S4S7S24S51A2S11S4A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run2__R <: run2__R = Some [mkLeafA E2 RsCut]). Qed.
Lemma efr_isl : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS24S4eS27A3ScG0S31A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_isl)). Qed.
Lemma chk_isl : ltac2:(tb__ "0|0|
S0SaS4aS24S4eS27S31S48S4S3S6S50A4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_isl : ltac2:(tb__ "0|0|
S0S3S4cS27S4eS4fS24S31A5S2aA3"). Proof. vm_cast_no_check (eq_refl T3). Qed.
Lemma fsS : ltac2:(tb__ "0|0|
S0SaS3fS3eS2S36A1A2SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run3s : ltac2:(tb__ "0|0|
S0SdS3A1S40S3eS36A2ScS3S30A2A3"). Proof. vm_cast_no_check (eq_refl (Some E6s)). Qed.
Lemma xf6s : ltac2:(tb__ "0|0|
S0SdS3A1S59S30S10S5aS5bU1S1cN400A1A2S11S5aA1A3A2ScS3S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some E6sS)). Qed.
Lemma efr_sis : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS26S43S2eA3ScG0S34A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_sis)). Qed.
Lemma chk_sis : ltac2:(tb__ "0|0|
S0SaS4aS26S43S2eS34S48S4S3S6S45A4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_sis : ltac2:(tb__ "0|0|
S0S3S4cS2eS43S44S26S34A5S2cA3"). Proof. vm_cast_no_check (eq_refl T7s). Qed.
Lemma run3b : ltac2:(tb__ "0|1|
S0SdSeS4A1M0A1S5S3aUbb8S3bS35SbA5ScG0S10S4S7S29S51A2S11S4A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run3b__R <: run3b__R = Some [mkLeafA E4 RsCut]). Qed.
Lemma split4 : ltac2:(tb__ "0|1|
S0SdS17A1S5cS17S17S58S2S29A1U1M0S1cN930A1A3S17S58R1G0S1cN980A1A3LS1;A4ScS17S2S22A1A2A3").
Proof. vm_cast_no_check (eq_refl (Some (ax_S E4S))). Qed.
Lemma efr_rip : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS22S4dS39A3ScG0S32A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_rip)). Qed.
Lemma chk_rip : ltac2:(tb__ "0|0|
S0SaS4aS22S4dS39S32S48S4S3S6S5eA4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_rip : ltac2:(tb__ "0|0|
S0S3S4cS39S4dS5dS22S32A5S37A3"). Proof. vm_cast_no_check (eq_refl T5). Qed.
Lemma fsB : ltac2:(tb__ "0|0|
S0SaS3fS3dS2S38A1A2SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run5 : ltac2:(tb__ "0|0|
S0SdS3A1S40S3dS38A2ScS3S2fA2A3"). Proof. vm_cast_no_check (eq_refl (Some E6b)). Qed.
Lemma xf6b : ltac2:(tb__ "0|0|
S0SdS3A1S59S2fS42A2ScS3S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some E6bS)). Qed.
Lemma efr_sib : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS25S43S2dA3ScG0S33A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_sib)). Qed.
Lemma chk_sib : ltac2:(tb__ "0|0|
S0SaS4aS25S43S2dS33S48S4S3S6S45A4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_sib : ltac2:(tb__ "0|0|
S0S3S4cS2dS43S44S25S33A5S2bA3"). Proof. vm_cast_no_check (eq_refl T7b). Qed.

Lemma shapes : ltac2:(tb__ "0|10|
S1S0SaS15S2S23A1M0A1SfA3S1S0S20S13G0A1S53A3S1S0S20S13S2S28A1M1A1S53A3S1S0SaS15G1A1SfA3S1S0S21S1eG1A1S5fA3S1S0S20S13S2S24A1A1S53A3S1S0S1bS49S27P10M2A2S16G2A1M3A3S1S0S1bS49S27PcA2S57A3S1S0S20S13S2S2aA1M4A1P8dM5A3S1S0SaS54S14S1dS18S16P8cA1G3A2A1S1aG4A1A3SbA3S1S0SaS15S2S36A1A1SfA3S1S0SaS15S2S35A1A1SfA3S1S0S20S13S2S30A1A1M6S13S2S26A1A1A3S1S0SaS47G5G6A2SbA3S1S0S1bS49S2eG2A2G3A3S1S0S20S13S2S29A1A1M7S13S2S22A1A1A3S1S0SaS47G5G7A2SbA3S1S0S20S13S2S37A1A1M8S46G7P28M9A2A3S1S0SaS15S2S38A1A1SfA3S1S0S20S13S2S2fA1A1MaS13S2S25A1A1A3S1S0SaS47G8GaA2SbA3S1S0S1bS49S2dG2A2G3A3S1S0S20S41S2cA1MbS46G6G9A2A3S1S0S20S13S2S2cA1McA1S46G6P29MdA2A3S1S0S20S41S2bA1MeS46GaG9A2A3S1S0S20S13S2S2bA1MfA1S46GaGdA2A3S1S0SaS54S14S1dS18S16GbA1G3A2A1S1aGcA1A3SbA3S0SaS54S14S1dS18S16GeA1G3A2A1S1aGfA1A3SbA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End FpsD_st.

(* [comment removed for export] *)
Module FpsU_st.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "sym_runA"; "la_state"; "mkLeafA"; "ax_setS"; "axwf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "Some"; "option"; "list"; "false"; "cons"; "nil"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sprop"; "ss_lenient"; "SVar"; "sstate"; "SPEq"; "sobj"; "ss_facts"; "sv"; "SLit"; "sprop_eqb"; "ss_pc"; "swf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsU_st"; "E4S"; "Pre"; "E2"; "E6bS"; "E6sS"; "s_isl"; "E1"; "E4"; "T3"; "T7b"; "T7s"; "s_sib"; "s_sis"; "E6b"; "E6s"; "R_isl"; "R_rip"; "R_sib"; "R_sis"; "T3B"; "T3S"; "T5"; "T5F"; "s_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "CUTS_FPS"; "facts_fps"; "FSB"; "FSS"; "fs_ok"; "runp"; "zvar"; "XF6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st"; "Pre_si"; "P_si"; "Posts_si"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen"; "Pre_isl"; "P_isl"; "Posts_isl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.Lists.List"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsB"; "factsS"; "sX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates"; "obindW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen.ISLAddr"; "isl_entry"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition Pre : axst := Pre_fps FMT_USAGE 0x16080 0x80.

Definition run1__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S3aU7d0S3bS23SbA5").
Local Strategy expand [run1__R].
Definition E1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => lf0 Pre (ro1__) 0) run1__R).
Definition run2__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S3aUbb8S3bS28SbA5").
Local Strategy expand [run2__R].
Definition E2 := Eval vm_compute in ((fun ro2__ : option (list leafA) => lf0 E1 (ro2__) 0) run2__R).
Definition s_isl := Eval vm_compute in ((16%positive, SVar 16) :: infer_sub 10 (ax_S E2) (ax_S Pre_isl)).
Definition R_isl := Eval vm_compute in match entails_frA E2 Pre_isl s_isl with Some R => R | None => [] end.
Definition T3 := Eval vm_compute in import_postA s_isl Pre_isl P_isl E2 R_isl.

Definition T3S : axst := ltac2:(tb__ "0|0|
S52S12S14S56S3cA3S2aA2").
Definition E6s := Eval vm_compute in match runp FSS T3S with Some A => A | None => T3S end.
Definition E6sS := Eval vm_compute in match apply_axforms E6s [AXSplit 1 (SLit (-1024))] with Some A => A | None => E6s end.
Definition s_sis := Eval vm_compute in ([(16%positive, SVar 16); (17%positive, SVar 17); (20%positive, SVar 20)] ++ infer_sub 10 (ax_S E6sS) (ax_S Pre_si)).
Definition R_sis := Eval vm_compute in match entails_frA E6sS Pre_si s_sis with Some R => R | None => [] end.
Definition T7s := Eval vm_compute in import_postA s_sis Pre_si P_si E6sS R_sis.

Definition T3B : axst := ltac2:(tb__ "0|0|
S52S12S14S55S3cA3S2aA2").
Definition run3b__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S3aUbb8S3bS35SbA5").
Local Strategy expand [run3b__R].
Definition E4 := Eval vm_compute in ((fun ro3__ : option (list leafA) => lf0 T3B (ro3__) 0) run3b__R).
Definition E4S := Eval vm_compute in
  match split_obj_at (ax_S E4) 1 (SLit (-2352)) with Some S1 =>
  match split_obj_at S1 1 (SLit (-2432)) with Some S2 => ax_setS E4 S2 | None => E4 end | None => E4 end.
Definition s_rip := Eval vm_compute in ((16%positive, vXL8) :: infer_sub 10 (ax_S E4S) (ax_S Pre_rip)).
Definition R_rip := Eval vm_compute in match entails_frA E4S Pre_rip s_rip with Some R => R | None => [] end.
Definition T5 := Eval vm_compute in import_postA s_rip Pre_rip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.P_ret E4S R_rip.
Definition T5F : axst := ltac2:(tb__ "0|0|
S52S10S14S18S16P8cA1S16P10A1A2S12S14S55S3cA3A3S37A2").
Definition E6b := Eval vm_compute in match runp FSB T5F with Some A => A | None => T5F end.
Definition E6bS := Eval vm_compute in match apply_axforms E6b XF6 with Some A => A | None => E6b end.
Definition s_sib := Eval vm_compute in ([(16%positive, SVar 16); (17%positive, SVar 17); (20%positive, SVar 20)] ++ infer_sub 10 (ax_S E6bS) (ax_S Pre_si)).
Definition R_sib := Eval vm_compute in match entails_frA E6bS Pre_si s_sib with Some R => R | None => [] end.
Definition T7b := Eval vm_compute in import_postA s_sib Pre_si P_si E6bS R_sib.

Lemma pre_wf : ltac2:(tb__ "0|0|
S1S0SaS9S23A1SbA3S0SaS1fS2S23A1A1SbA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pre_facts : ltac2:(tb__ "0|0|
S0SeS14A1S1aS2S23A1A1S3cA3"). Proof. reflexivity. Qed.
Lemma xs4 : ltac2:(tb__ "0|0|
S0S3S8S29S2S22A1A2S22A3"). Proof. reflexivity. Qed.
Lemma lenT7 : ltac2:(tb__ "0|0|
S1S0SaS15S2S2cA1A1SfA3S0SaS15S2S2bA1A1SfA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma run1 : ltac2:(tb__ "0|1|
S0SdSeS4A1M0A1S5S3aU7d0S3bS23SbA5ScG0S10S4S7S28S51A2S11S4A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run1__R <: run1__R = Some [mkLeafA E1 RsCut]). Qed.
Lemma run2 : ltac2:(tb__ "0|1|
S0SdSeS4A1M0A1S5S3aUbb8S3bS28SbA5ScG0S10S4S7S24S51A2S11S4A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run2__R <: run2__R = Some [mkLeafA E2 RsCut]). Qed.
Lemma efr_isl : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS24S4eS27A3ScG0S31A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_isl)). Qed.
Lemma chk_isl : ltac2:(tb__ "0|0|
S0SaS4aS24S4eS27S31S48S4S3S6S50A4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_isl : ltac2:(tb__ "0|0|
S0S3S4cS27S4eS4fS24S31A5S2aA3"). Proof. vm_cast_no_check (eq_refl T3). Qed.
Lemma fsS : ltac2:(tb__ "0|0|
S0SaS3fS3eS2S36A1A2SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run3s : ltac2:(tb__ "0|0|
S0SdS3A1S40S3eS36A2ScS3S30A2A3"). Proof. vm_cast_no_check (eq_refl (Some E6s)). Qed.
Lemma xf6s : ltac2:(tb__ "0|0|
S0SdS3A1S59S30S10S5aS5bU1S1cN400A1A2S11S5aA1A3A2ScS3S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some E6sS)). Qed.
Lemma efr_sis : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS26S43S2eA3ScG0S34A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_sis)). Qed.
Lemma chk_sis : ltac2:(tb__ "0|0|
S0SaS4aS26S43S2eS34S48S4S3S6S45A4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_sis : ltac2:(tb__ "0|0|
S0S3S4cS2eS43S44S26S34A5S2cA3"). Proof. vm_cast_no_check (eq_refl T7s). Qed.
Lemma run3b : ltac2:(tb__ "0|1|
S0SdSeS4A1M0A1S5S3aUbb8S3bS35SbA5ScG0S10S4S7S29S51A2S11S4A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run3b__R <: run3b__R = Some [mkLeafA E4 RsCut]). Qed.
Lemma split4 : ltac2:(tb__ "0|1|
S0SdS17A1S5cS17S17S58S2S29A1U1M0S1cN930A1A3S17S58R1G0S1cN980A1A3LS1;A4ScS17S2S22A1A2A3").
Proof. vm_cast_no_check (eq_refl (Some (ax_S E4S))). Qed.
Lemma efr_rip : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS22S4dS39A3ScG0S32A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_rip)). Qed.
Lemma chk_rip : ltac2:(tb__ "0|0|
S0SaS4aS22S4dS39S32S48S4S3S6S5eA4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_rip : ltac2:(tb__ "0|0|
S0S3S4cS39S4dS5dS22S32A5S37A3"). Proof. vm_cast_no_check (eq_refl T5). Qed.
Lemma fsB : ltac2:(tb__ "0|0|
S0SaS3fS3dS2S38A1A2SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run5 : ltac2:(tb__ "0|0|
S0SdS3A1S40S3dS38A2ScS3S2fA2A3"). Proof. vm_cast_no_check (eq_refl (Some E6b)). Qed.
Lemma xf6b : ltac2:(tb__ "0|0|
S0SdS3A1S59S2fS42A2ScS3S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some E6bS)). Qed.
Lemma efr_sib : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS25S43S2dA3ScG0S33A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_sib)). Qed.
Lemma chk_sib : ltac2:(tb__ "0|0|
S0SaS4aS25S43S2dS33S48S4S3S6S45A4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_sib : ltac2:(tb__ "0|0|
S0S3S4cS2dS43S44S25S33A5S2bA3"). Proof. vm_cast_no_check (eq_refl T7b). Qed.

Lemma shapes : ltac2:(tb__ "0|10|
S1S0SaS15S2S23A1M0A1SfA3S1S0S20S13G0A1S53A3S1S0S20S13S2S28A1M1A1S53A3S1S0SaS15G1A1SfA3S1S0S21S1eG1A1S5fA3S1S0S20S13S2S24A1A1S53A3S1S0S1bS49S27P10M2A2S16G2A1M3A3S1S0S1bS49S27PcA2S57A3S1S0S20S13S2S2aA1M4A1P8dM5A3S1S0SaS54S14S1dS18S16P8cA1G3A2A1S1aG4A1A3SbA3S1S0SaS15S2S36A1A1SfA3S1S0SaS15S2S35A1A1SfA3S1S0S20S13S2S30A1A1M6S13S2S26A1A1A3S1S0SaS47G5G6A2SbA3S1S0S1bS49S2eG2A2G3A3S1S0S20S13S2S29A1A1M7S13S2S22A1A1A3S1S0SaS47G5G7A2SbA3S1S0S20S13S2S37A1A1M8S46G7P28M9A2A3S1S0SaS15S2S38A1A1SfA3S1S0S20S13S2S2fA1A1MaS13S2S25A1A1A3S1S0SaS47G8GaA2SbA3S1S0S1bS49S2dG2A2G3A3S1S0S20S41S2cA1MbS46G6G9A2A3S1S0S20S13S2S2cA1McA1S46G6P29MdA2A3S1S0S20S41S2bA1MeS46GaG9A2A3S1S0S20S13S2S2bA1MfA1S46GaGdA2A3S1S0SaS54S14S1dS18S16GbA1G3A2A1S1aGcA1A3SbA3S0SaS54S14S1dS18S16GeA1G3A2A1S1aGfA1A3SbA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End FpsU_st.

(* [comment removed for export] *)
Module Fps_tail.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "andb"; "bool"; "option"; "nil"; "app"; "list"; "negb"; "false"; "true"; "length"; "None"; "pair"; "orb"; "prod"; "Some"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SLit"; "SVar"; "sobj"; "sstate"; "SPUle"; "ss_next"; "SAlu"; "sv_eqb"; "SPNot"; "ss_objs"; "SPBranch"; "swf"; "SPAlign"; "SPEq"; "ob_dflt"; "ss_pc"; "DList"; "FcsrFrm0"; "SExt"; "SLBytes"; "cell"; "dflt_writable"; "is_arr"; "mkSS"; "ob_cells"; "ob_hi"; "ob_lo"; "sprop_eqb"; "ss_facts"; "ss_lenient"; "ss_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_base"; "ax_X"; "ax_setS"; "axwf"; "dflt_eqb"; "entailsA"; "la_reason"; "la_state"; "mkLeafA"; "sobj_eqb"; "sym_runA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XMerge"; "XRebase"; "XSelect"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "BASEF"; "facts_fps"; "runp"; "fs_ok"; "zvar"; "set_facts"; "trim"; "CUTS_FPS"; "FUEL_T"; "O_fwin"; "STRP"; "TPL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "BLit"; "BSrc"; "cells_bytes"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "add"; "of_nat"; "pow"; "sub"; "to_nat"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "tailA_out"; "NULF"; "P_fps"; "aln"; "WS"; "WZ"; "ALIGN"; "T8"; "ZLIT"; "small_facts"; "tailA_post"; "FA1"; "FA5"; "FA6"; "FPA"; "FQA"; "FWSMALL"; "TAO"; "WX"; "XQ1"; "XQ2"; "XW"; "bexps_eqb"; "blA"; "dropL"; "junk_fps"; "objs_fps'"; "post_regs_fps"; "post_sub"; "seg"; "splitsA"; "subA"; "tailA"; "tailA_n"; "tailA_ok"; "x_ok"; "xr_norl"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "BC_EQ"; "BC_GEU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "add"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates"; "obindW"; "axc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "vXL"; "sX"; "vXB"; "vXO"; "O_cfsl"; "O_realmc"; "O_realsn"; "O_strS"; "@Corelib.Lists.ListDef"; "map"; "seq"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err.WLerrS"; "Pre_wl2"; "D"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "sv_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXRebase"; "AXSelect"; "apply_axforms"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "two62"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "A_globals"; "mkA"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface"; "fp_ret"; "O_ferr2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface"; "FERR"; "NPOST_FW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut";
"set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ListCommitA"; "exts_rl_free"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates"; "O_b2e"; "finish_fp"; "unlist_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "O_cflag"; "O_realm"; "O_realv"; "O_rtc2"; "O_ssp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "HSE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymBytes SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform ListCommitA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition NULF (z : sv) : sprop := ltac2:(tb__ "0|0|
S1fS21S8cS29S9Q8S2aP3Vz;Z1A3A3S17Z0A1A3A1").
Definition ZLIT (v : positive) (n : Z) : list sprop := ltac2:(tb__ "0|2|
S0S15S1bS18Vv;A1M0S17Vn;A1M1A2S0S15S1bG1G0A2S5S15A1A3A3").
Definition aln (k : Z) : sprop := ltac2:(tb__ "0|1|
S21S8aS1dS89S3S16L_;S5aVk;Z0M0A2S96S1dS88S96S17Vk;A1A3X3x2S17Z3A1A3S17G0A1A3").
Definition ALIGN (r : Z) : list sprop := ltac2:(tb__ "0|a|
S3S7S15A1L_;M0S5aVr;Z0M1A2S0S15S66G1A1M2S5S15A1M3A3G0S5aVr;Z1M4A2S0S15S1fG2A1M5S0S15S1fS66G4A1M6A1M7S0S15S1fS66Z2M8A1M9A1S0S15S66Z3A1G3A3A3A3A3G0S5aVr;G8A2S0S15G5S0S15G7S0S15G9G3A3A3A3S0S15G5S0S15G6G3A3A3X3x2X3x2X3x2").

Definition FWSMALL (a : Z) (v : positive) : sprop := ltac2:(tb__ "0|0|
S21S8bS17S5eZ50Va;A2A1S18Vv;A1A3").
Definition FWBIG (a : Z) (v : positive) : sprop := SPNot (FWSMALL a v).
Definition small_facts (a n r : Z) (v : positive) (cls : list sprop) : list sprop := ltac2:(tb__ "0|0|
S6S15S0S15S64S18Vv;A1A1S0S15S64S17Vn;A1A1S0S15S73Va;Vv;A2S5S15A1A3A3A3S6S15S6bVv;Vn;A2S6S15S69Vr;A1S6S15Vcls;S4bA3A3A3A3").
Definition T8 (a n r : Z) (cls : list sprop) (T7 : axst) : axst := ltac2:(tb__ "0|0|
S8eS6cVa;Vn;Vr;S4eVT7;A1Vcls;A5VT7;A2").

Definition XW : list axform := ltac2:(tb__ "0|1|
S0Sa5Sa7U0M0A1S0Sa5Sa8S0S1G0S0S1U9S0S1UaS0S1U1S0S1U2S0S1U3S0S1U4S0S1U5S0S1U6S0S1UbS0S1UcS0S1UdS0S1UeS0S1U7S0S1U8S5S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0Sa5Sa6G0A1S5Sa5A1A3A3A3").

Definition seg (fuel : nat) (A : axst) (pc : Z) : option axst := ltac2:(tb__ "0|4|
S4S7S38A1M0A1S4S36A1M1Lx;S43Sb4Vfuel;S51VA;SaA5G0G0G1Ll;R1ScS36A1M2S38G0G0G1Ll0;R1SbcG1Lx;S3fR2A1G2S3G1L_;S5aS26S37S40R2A1M3A1A1Vpc;A2S10S36G3A2G2X3x2G2G2G2G2G2Xbcx7S38G0G2Ll2;Ll1;X7x2Ll0;LL;X7x2Ll;G2X4x2").

Definition splitsA (e : Z) (S : sstate) : option sstate := ltac2:(tb__ "0|0|
S93S1aS1aS8dVS;U0S17N248A1A3S1aS93S1aS1aS8dR1U1S17N228A1A3S1aS93S1aS1aS8dR1U2S17N1d0A1A3S1aS93S1aS1aS8dR1U3S17Ve;A1A3S1aS93S1aS1aS8dR1U5S17S5bSb7Z78A2A1A3S1aS8dR1U6S17S5bSb7Z7cA2A1A3LS5;A4LS4;A4LS3;A4LS2;A4LS1;A4").
Definition subA (len : Z) (Cs : sstate) : wsub := ltac2:(tb__ "0|3|
S6SfS14S16A2M0S0G0SdS14S16PcS1dS88S18PaM1A1S17N1d0A1A3A4S0G0SdS14S16PdS17Vlen;A1A4S0G0SdS14S16PeS17Z0A1M2A4S0G0SdS14S16PfG2A4S5G0A1A3A3A3A3SccG1VCs;S37Sa1A1A3A3").

Definition blA (pre : list Z) (n : Z) (suf : list Z) : list bexp := ltac2:(tb__ "0|0|
S6S56S9dS13S56S57Vpre;A4S6S56S9dS1S56S1S58P3S5cR1A1A2Li;S9eU0S5fVn;A1A2A4S9dS13S56S57Vsuf;A4A3A3").
Definition bexp_eqb (a b : bexp) : bool := ltac2:(tb__ "0|1|
S56S3La;Va;S13S56S3Lb;M0Vb;S13S5aR2R1A2Ly;S14S13S9Li;Ll;X56x2Lx;S14S13G0Vb;S13S9Lz;S14S13S2S8fR4R2A2S5aR3R1A2A2Li';Ll';X56x2Li;Ll;X56x2").
Fixpoint bexps_eqb (a b : list bexp) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => bexp_eqb x y && bexps_eqb a' b' | _, _ => false end.

Definition XQ1 : list xform := ltac2:(tb__ "0|1|
S0S45S48S6S1S0S1U0S0S1U1S0S1U3S5S1A1M0A3A3A3S6S1S9eU4U11A2S0S1U2G0A3A3A3A1S5S45A1A3").
Definition dropL (S : sstate) : sstate := ltac2:(tb__ "0|1|
SbeVS;S9fS19Sc1SbS19S20VS;A1M0A2U1A2G0A3A2").
Definition XQ2 : list xform := ltac2:(tb__ "0|5|
S0S45S47U0M0A1S0S45S47U1M1A1S0S45S48S0S1U3S0S1G0S0S1U4S0S1G1S0S1U5S0S1U8S0S1U6S0S1U2M2S0S1U7S0S1U9S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U13S5S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S45S46G0A1M3S0S45G3S0S45G3S0S45G3S0S45S46G2A1M4S0S45G4S5S45A1A3A3A3A3A3A3A3A3A3").

Definition post_reg_fps (r : nat) : sv := ltac2:(tb__ "0|1|
S1S16Lr;Vr;S17Z0A1S1S1S16Ln;R1S18PbA1S1S1S16Ln0;R1S18PaA1S1S1S16Ln1;R1S17Z10800A1S1S1S16Ln2;R1S17S55A1S1S1S16Ln3;R1S18S91P64S92Vr;A1A2A1M0S1S1S16Ln4;R1G0S1S1S16Ln5;R1G0S1S1S16Ln6;R1S18P1cA1S1S1S16Ln7;R1S18P1dA1S1S1S16Ln8;R1G0S1S1S16Ln9;R1G0S1S1S16Ln10;R1G0S1S1S16Ln11;R1G0S1S1S16Ln12;R1G0S1S1S16Ln13;R1G0S1S1S16Ln14;R1G0S1S1S16Ln15;R1G0S1S1S16Ln16;R1S18P26A1S1S1S16Ln17;R1S18P27A1S1S1S16Ln18;R1S18P28A1S1S1S16Ln19;R1S18P29A1S1S1S16Ln20;R1S18P2aA1S1S1S16Ln21;R1S18P2bA1S1S1S16Ln22;R1S18P2cA1S1S1S16Ln23;R1S18P2dA1S1S1S16Ln24;R1S18P2eA1S1S1S16Ln25;R1S18P2fA1S1G0Ln26;X1x2Ln25;X1x2Ln24;X1x2Ln23;X1x2Ln22;X1x2Ln21;X1x2Ln20;X1x2Ln19;X1x2Ln18;X1x2Ln17;X1x2Ln16;X1x2Ln15;X1x2Ln14;X1x2Ln13;X1x2Ln12;X1x2Ln11;X1x2Ln10;X1x2Ln9;X1x2Ln8;X1x2Ln7;X1x2Ln6;X1x2Ln5;X1x2Ln4;X1x2Ln3;X1x2Ln2;X1x2Ln1;X1x2Ln0;X1x2Ln;X1x2").
Definition post_regs_fps : list sv := map post_reg_fps (seq 0 32).
Definition objs_fps' : list sobj := ltac2:(tb__ "0|0|
S6S19S0S19S53S0S19S9cS0S19Sb6S0S19ScaS0S19Sc8S0S19Sc5S0S19Sc7S0S19Sc6S0S19S9aS0S19S9bS0S19S99S0S19Sc9S5S19A1A3A3A3A3A3A3A3A3A3A3A3A3Sb2A3").
Definition P_fps : axst := ltac2:(tb__ "0|0|
Sb3S2eSb5S7eSafS28ScS16A1S7dS4bSb8S9A9S5SfS16S16A2A1A2").
Definition Posts_fps : list leafA := ltac2:(tb__ "0|0|
S0S38S41S65SbdA2S5S38A1A3").
Definition junk_fps : list nat := ltac2:(tb__ "0|0|
S0S1U5S0S1U6S0S1U7S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U1cS0S1U1dS0S1U1eS0S1U1fS5S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition post_sub (S : sstate) : wsub := ltac2:(tb__ "0|0|
S9dS1SfS14S16A2S1SdS14S16S91P64S92R1A1A2Sa0S16R1S35VS;A1S17Z0A1A4A4Lr;S7cA4").

Record tailA_out := TAO { ta_W : axst; ta_S6 : sstate; ta_Cs : sstate; ta_s : wsub; ta_R : list sobj; ta_T : axst;
                          ta_F : axst; ta_G1 : sstate; ta_G2 : sstate; ta_G2u : sstate; ta_G3 : sstate; ta_sp : wsub }.

Definition xr_norl (r : sv * sv) : bool := ltac2:(tb__ "0|4|
S8SeSeSeSa4P5M0S11S16S16Vr;A3M1A2Sa4P6M2G1A2A2Sa4G0S12S16S16Vr;A3M3A2A2Sa4G2G3A2A2A1").
Definition x_ok (W : axst) (nx : positive) : bool := ltac2:(tb__ "0|2|
S2S2SaaSfS16S16A2M0S87S3aVW;A1M1A3SaaG0S44Vnx;A1G1A3A2S1eS39VW;A1S17Sb1A1A2A2").

Definition tailA_post (pre suf : list Z) (n len : Z) (T8 : axst) (W0 : axst) : option tailA_out := ltac2:(tb__ "0|1b|
S3S4S63A1M0L_;M1S8S2S5aS26S37VW0;A1M2A1Zd6760A2S90S1cS37VT8;A1A1M3S1cG2A1A2A2A1ScS63A1M4S4S36A1G0Lx;M5Sa9S4fVW0;S4bA2S78A2S36G1S8S2SaaS15S15SadS15S32R1A1S33S37R2A1M6A1A3Lf;S4bA3S90G3S1cS37R1A1M7A1A2A2A1G4S4S1aA1G0Lx;M8S81S5bN1d0M9Vlen;A2MaG7A2S1aS4S19A1G0Lx;MbSabS19S20R1A1McU3MdA3S19S4S7S56A1MeA1G0Lx;S59S2fR1A1MfS17G9A1M10Z0M11S5fVlen;A1A4GeG1S8S2S2S2S2S2S2S2S2S79R1S7aVpre;Vn;Vsuf;A3A2S8Sa3P5M12R3A2A1A2S8Sa3P6M13R3A2A1A2S2cS25R2A1M14A1A2S8S2dG14A1A1A2S1eS31R2A1G10A2A2S1eS30R2A1S17GaA1A2A2SbfG12S20R3A1M15A2A2SbfG13G15A2A2A1G4Sc3R3A1S1aS3bR5R1A2S36S82Vlen;R2A2Sb9G1S8S86R7S1cR3A1M16A2A1G4S4S7S19A1M17A1G0Lx;SceR2Sa1R1A3G17G1S8S2S2S2S2S2S2ScdR3Sa1R2R1S0S36Sa2S5S36A1A3A5S22R4A1A2S1eSbaR2PdA2S17Vlen;A1A2A2S1eSbaR2PfA2S17G11A1A2A2S8fS1cR4A1S1cS37R8A1A1M18A2A2S8fS1cSd0R7GdG12A3A1G18A2A2S8fS1cR7A1G18A2M19A2A1G4ScfR2Sa1Sa2R3R1A5S36S8eS4aR1A2S36G1SeS34G7A1S8S90SaeS1cG6A1A2A1A2G4G5S80S52R1Sb5A3S36S8eS4bR1A2S36G8S49G7S76A2S1aGbSabS19GcU14A3S19G1S8S2S42R1Sc2A2Sc0SbS19S20R2A1A2U15A2A2A1G4S7bR2A1S1aGbSabS19GcU1M1aA3S19G1S8S2S3dS25R1A1S27G12A1A2Sc0SbS2bGfA2U0A2A2A1G4Sc4R2G1aA2S1aG1S8S22R1A1A1G4G8S49R1S77A2S1aS7fR1A1Sb9G1S2S2S2S2S2S2S2S2S3eS94R2A1S65R1A3SbbR1SaeA2A2S8Sa3G12R2A2A1A2S8Sa3G13R2A2A1A2S1eS39R8A1S17Sb1A1A2A2S90SaeG18A2A2G19A2S8fG16G18A2A2S8fS1cR2A1G18A2A2S10S63S74R13R12RfRdRcRbR9R7R5R3R2R1AcA2G4X3x2Tsp;LG3;G4X4x2X3x2TG2u;X3x2Lob1;G4X4x2TG2;X3x2Lob2;G4X4x2LG1;G4X4x2TF;LF0;G4X4x2X3x2TTf;TT;X3x2LR;G4X4x2X3x2Ts;TC;TCs;X3x2Lbl;G4X4x2Lo8;G4X4x2LS6;G4X4x2X3x2LW;G4X4x2X3x2").
Definition tailA (Fs : list (list sprop)) (pre suf : list Z) (n len : Z) (T8 : axst) : option tailA_out := ltac2:(tb__ "0|5|
S3S4S63A1M0L_;M1S8S5aVlen;S5bS5bS5cSbS13Vpre;A2A1Vn;A2S5cSbS13Vsuf;A2A1A2A2A1ScS63A1M2G1S8S2S4dVFs;S37VT8;A1M3A2S4dS0S7S15A1M4S4bS5G4A1A3G3A2A2A1G2S4S36A1G0Lx;S4cVFs;VT8;A2S36S6dVpre;Vsuf;Vn;Vlen;VT8;R1A6LW0;G2X4x2X3x2X3x2").
Definition tailA_ok (Fs : list (list sprop)) (pre suf : list Z) (n len : Z) (T8 : axst) : bool := ltac2:(tb__ "0|0|
S4S63A1S3Lx;S83VFs;Vpre;Vsuf;Vn;Vlen;VT8;A6S63SaLt;S9X4x2").

Definition tailA_n (FsP : list (list sprop)) (FsQ : Z -> list (list sprop)) (pre suf : list Z) (n len : Z) (T8s : Z -> axst) (rs : list Z) : bool := ltac2:(tb__ "0|6|
S7S13A1M0S3Lrs;Vrs;SaS13G0S4S36A1S3Lx;M1S4cVFsP;VT8s;R2A1M2A2S36SaaS13S13S2S2S2S5aVlen;S5bS5bS5cSbS13Vpre;A2A1Vn;A2S5cSbS13Vsuf;A2A1A2A2S4dS6S7S15A1M3VFsP;VFsQ;R1A1M4A3S37VT8s;R1A1A1M5A2A2S4dS0G3S4bS5G3A1A3G5A2A2G1S4cG4R2A2S36S4S63A1S3Lx;S6dVpre;Vsuf;Vn;Vlen;G2R1A6S63SaLt;S9X4x2LW0;S9X4x2A2Lr;Vrs;A3LM;S9X4x2Ll;Lr0;X7x2").

Lemma set_facts_add_facts : ltac2:(tb__ "0|1|
S7S15A1M0S36G0S60S36S4fS8eR3R2A2R1A2S4fR2R1A2A3FF;FA;FL;").
Proof. intros L A F. reflexivity. Qed.
Lemma trim_add_facts : ltac2:(tb__ "0|1|
S7S15A1M0G0S36S60S36S50R3S8eR2R1A2A2S50R3R1A2A3FA;FL;FF;").
Proof. intros F L A. unfold trim. rewrite set_facts_add_facts. reflexivity. Qed.
Lemma runp_cons_add_facts : ltac2:(tb__ "0|2|
S7S15A1M0S7G0A1G0S36S60S4S36A1S4cS0G0R4R3A3M1S8eR2R1A2A2S4cG1R1A2A3FA;FL;FFs;FF;").
Proof. intros F Fs L A. cbn [runp]. rewrite trim_add_facts. reflexivity. Qed.
Lemma runp_app : ltac2:(tb__ "0|4|
S7S7S15A1M0A1M1G1S36S60S4S36A1M2S4cS6G0R3R2A3R1A2G2G2Lx;S4cR3R1A2M3S36G3LM;ScS36A1X4x2A3FA;FQ;FP;").
Proof.
  induction P as [|F P IH]; intros Q A; [reflexivity|]. cbn [runp app]. destruct (seg0 (trim F A)) as [B|]; [apply IH | reflexivity].
Qed.
Lemma tailA_n_sound : ltac2:(tb__ "0|3|
S7S7S15A1M0A1M1S13G1F_;S7S13A1M2G2S13S13S13G0S36G2S13S62S60G1RbS5G0A1A3A1S60S3S84RcRbRaR9R8R7S13S6aR7R9R1R6R5A5Lr;R3A8SaA3SacS13R3R4A3S60S3S85S6G0ReRdR4A1A3RcRbRaR9S6aR8RaR4R7R6A5A6SaA3F_;F_;F_;Fr;Frs;FT7;Fcls;Fa;Flen;Fn;Fsuf;Fpre;FFsQ;FFsP;").
Proof.
  intros FsP FsQ pre suf n len a cls T7 rs r HP H Hin. unfold tailA_n in H. destruct rs as [|r0 rs']; [destruct Hin|].
  assert (EP : forall r1 r2, runp FsP (T8 a n r1 cls T7) = runp FsP (T8 a n r2 cls T7)).
  { intros r1 r2. destruct FsP as [|F P]; [congruence|]. unfold T8. rewrite !runp_cons_add_facts. reflexivity. }
  destruct (runp FsP (T8 a n r0 cls T7)) as [M|] eqn:EM; [|discriminate].
  pose proof (proj1 (forallb_forall _ _) H r Hin) as Hr. cbn beta in Hr.
  apply andb_prop in Hr as [Hr Hrun]. apply andb_prop in Hr as [Hr Hf2]. apply andb_prop in Hr as [Hlen Hf1].
  unfold tailA_ok, tailA. rewrite Hlen, Hf1, Hf2. cbn [negb andb]. rewrite runp_app, <- (EP r0 r), EM.
  destruct (runp (FsQ r) M) as [W0|]; [|discriminate]. destruct (tailA_post pre suf n len (T8 a n r cls T7) W0); [reflexivity | discriminate].
Qed.

Definition LEAN (a n r : Z) (cls : list sprop) (T7 : axst) : list sprop := ltac2:(tb__ "0|1|
S0S15S24S18S4eVT7;A1M0A1S18P10A1A2S6cVa;Vn;Vr;G0Vcls;A5A3").

Definition WZ (v : positive) (n : Z) : list sprop := ltac2:(tb__ "0|0|
S0S15S24S18Vv;A1S18P10A1A2S6bVv;Vn;A2A3").
Definition WS : list sprop := ltac2:(tb__ "0|3|
S6S15S0S15S1bS1dS88S18P10A1M0S17Z8A1M1A3S18P11A1M2A2S0S15S1bG1G2A2S0S15S1bG2S17Sb0A1A2S0S15S1bS1dS88G0S17Z10A1A3G2A2S5S15A1A3A3A3A3S54A3").
Definition WX : list sprop := ltac2:(tb__ "0|5|
S0S15S1bS1dS88S98S18P11A1M0A3S95A2S0S15S1bS98S95A2S0S15S1bG0S95A2S0S15S1bS95S17S5dZ2M1Z28A2A1A2S0S15S1bS17ScbA1S97A2S0S15S1bS1dS88S97S95A3M2S17S5dG1Z2fA2M3A1A2S0S15S1bS97S17S5eG3Z40A2A1A2S0S15S23P12Z6M4A2S0S15S23P13G4A2S0S15S1bS1dS88S96S17Z1A1A3G2A2S0S15S1bS18PaA1S96A2S5S15A1A3A3A3A3A3A3A3A3A3A3A3").
Definition FA1 (v : positive) (n : Z) : list sprop := ltac2:(tb__ "0|0|
S6S15S4aS6S15S68Vv;Vn;A2S6S15S67S0S15S64S18Vv;A1A1S0S15S64S17Vn;A1A1S5S15A1A3A3A3A3A3").
Definition FA5 (v : positive) (n : Z) : list sprop := ltac2:(tb__ "0|0|
S6S15S4aS6S15S68Vv;Vn;A2S6S15S67S75A3A3A3").
Definition FA6 (v : positive) (n r : Z) : list sprop := ltac2:(tb__ "0|0|
S6S15S4aS6S15S68Vv;Vn;A2S6S15S67S69Vr;A1A3A3A3").

Definition FPA (n : Z) (T7 : axst) : list (list sprop) := ltac2:(tb__ "0|2|
S0S7S15A1M0S6eS4eVT7;A1M1Vn;A2S0G0S4aS0G0S4aS0G0S4aS0G0S6fG1Vn;A2S5G0A1A3A3A3A3A3").
Definition FQA (n r : Z) (T7 : axst) : list (list sprop) := ltac2:(tb__ "0|1|
S0S7S15A1M0S70S4eVT7;A1Vn;Vr;A3S0G0S4aS0G0S4aS0G0S4aS0G0S4aS5G0A1A3A3A3A3A3").
Definition FTA (n r : Z) (T7 : axst) : list (list sprop) := ltac2:(tb__ "0|0|
S6S7S15A1S71Vn;VT7;A2S72Vn;Vr;VT7;A3A3").

Definition PRE_C : list Z := ltac2:(tb__ "0|4|
S0S13Z63M0S0S13Z6cS0S13Z69S0S13Z3aS0S13Z20M1S0S13G0S0S13Z61S0S13Z6eM2S0S13G2S0S13Z6fM3S0S13Z74S0S13G1S0S13G3S0S13Z70S0S13Z65S0S13G2S0S13G1S5S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition PRE_D : list Z := ltac2:(tb__ "0|4|
S0S13Z63S0S13Z6cS0S13Z69S0S13Z3aS0S13Z20M0S0S13Z72M1S0S13Z65M2S0S13Z61S0S13Z64S0S13G0S0S13G2S0S13G1S0S13G1S0S13Z6fM3S0S13G1S0S13G0S0S13G3S0S13Z6eS0S13G0S5S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition PRE_U : list Z := ltac2:(tb__ "0|0|
S0S13Z75S0S13Z73S0S13Z61S0S13Z67S0S13Z65S0S13Z3aS0S13Z20S5S13A1A3A3A3A3A3A3A3").
Definition SUF_NL : list Z := [10].
Definition SUF_U : list Z := ltac2:(tb__ "0|0|
S0S13Z20S0S13Z49S0S13Z4eS0S13Z50S0S13Z55S0S13Z54S0S13ZaS5S13A1A3A3A3A3A3A3A3").

Lemma P_fps_wf : ltac2:(tb__ "0|0|
S61S60S3S3cS65A1SaA3S60S3S22S37S65A1A1SaA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Fps_tail.

(* [comment removed for export] *)
Module Fps_run.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "Some"; "option"; "false"; "nil"; "cons"; "prod"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "ss_next"; "valuation"; "sprop_below"; "holds"; "ss_lenient"; "sstate"; "agree_below"; "obj_holds"; "smatch"; "swf"; "DUnknown"; "cell"; "ob_dflt"; "odefault"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "mkLeafA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "stableA"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_run"; "FsBelow"; "FsHold"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "runp"; "trim"; "fs_ok"; "setF"; "CUTS_FPS"; "FUEL_T"; "drop_cellsF"; "facts_in"; "prune0"; "seg0"; "set_facts"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import MuslWLA DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope. Open Scope Z_scope.

Local Opaque FUEL_T.

Lemma swf_setF : ltac2:(tb__ "0|0|
S12S0ScA1S9S1S16R2A1S2A3S9S1S27ScSfSdR3A1A1R2A3S2A3S9S1S16S35R4R3A2A1S2A3F_;F_;FF;FS;").
Proof.
  intros S F H HF. unfold swf in *. destruct S as [pc regs fregs fcsr resv objs facts nx lm]; cbn in *.
  apply andb_prop in H as [H _]. rewrite H, HF. reflexivity.
Qed.

Lemma smatch_setF : ltac2:(tb__ "0|0|
SeS12S0ScA1S8S0S3fA1S3eA2S28ScS10R4A1R2A3S9S1S27ScSfSdR4A1A1R3A3S2A3S15S1cR6R5R3A4S15S1cR7S35R6R5A2R4A4F_;F_;F_;Fm;FF;FS;Frho;").
Proof.
  intros rho S F m HF Hb Hsm. unfold smatch in *.
  destruct Hsm as (Hwf & Hpc & Hpend & Hidle & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  split; [apply swf_setF; assumption|].
  destruct S as [pc regs fregs fcsr resv objs facts nx lm]; cbn in *.
  repeat (split; [assumption|]). exact HF.
Qed.

Lemma SPA_set_facts : ltac2:(tb__ "0|0|
S24S1dS0ScA1SeS0S2cQ40A1A1S2dS28ScS10R3A1R4A3S9S1S27ScSfSdS1eR6A1A1A1R5A3S2A3S23S1cR8R7R5R4R3A6S23S1cR9S3cR8R7A2R6R5R4A6F_;F_;F_;Fw;Ftp;Frho;FF;FA;FJ;").
Proof.
  intros J A F rho tp w HF Hb [(Hsm & HMI & Hwf & Hsh & Hhz) Hk].
  split; [|exact Hk]. split; [|split; [exact HMI | split; [| split; [| exact Hhz]]]].
  - unfold set_facts. cbn [ax_S ax_setS]. apply smatch_setF; assumption.
  - unfold axwf in *. destruct A as [S X b]; cbn in *. exact Hwf.
  - unfold shadow_ok in *. destruct A as [S X b]; cbn in *. exact Hsh.
Qed.

Lemma obj_holds_drop_cells_unknown : ltac2:(tb__ "0|0|
SeS3dS18S1F_;S1bS9S1aS19R1A1S17A3S14S1cR5R4R2A4S14S1cR6R5S38R4R3A2A4F_;F_;Fo;Fkeep;Fms;Frho;").
Proof.
  intros rho ms keep o Hu (Hb & Hw & Hc & Hd & Hi). unfold drop_cellsF. rewrite Hu in *.
  split; [exact Hb|]. split; [exact Hw|]. split.
  - apply Forall_forall. intros c Hcin. apply filter_In in Hcin as [Hcin _]. exact (proj1 (Forall_forall _ _) Hc c Hcin).
  - split; [|exact I]. cbn [ob_dflt ob_cells ob_base ob_lo ob_hi]. intros off Hoff Hnc.
    assert (DEC : forall c, {in_cell rho off c} + {~ in_cell rho off c}).
    { intros c0. unfold in_cell. destruct (Z_le_dec (soff rho (c_off c0)) off); [destruct (Z_lt_dec off (soff rho (c_off c0) + c_width c0)); [left; lia | right; lia] | right; lia]. }
    destruct (Exists_dec (in_cell rho off) (ob_cells o) DEC) as [Hcov|Hncov]; [|exact (Hd off Hoff Hncov)].
    unfold SymState.covered in Hcov. apply Exists_exists in Hcov as (c & Hcin & Hin).
    pose proof (proj1 (Forall_forall _ _) Hc c Hcin) as (C1 & C2 & C3). unfold in_cell in Hin.
    assert (Hnw : bv_unsigned (oaddr rho (ob_base o) (soff rho (c_off c))) + Z.of_nat (Z.to_nat (c_width c)) <= 2 ^ 64).
    { unfold oaddr. rewrite Z_to_bv_unsigned. unfold obj_lo_of, obj_hi_of in *.
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia. }
    pose proof (rd_bytes_nth _ _ _ _ (Z.to_nat (off - soff rho (c_off c))) C3 ltac:(lia) Hnw) as R.
    unfold dflt_holds.
    replace (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off))
      with (Z_to_bv 64 (bv_unsigned (oaddr rho (ob_base o) (soff rho (c_off c))) + Z.of_nat (Z.to_nat (off - soff rho (c_off c))))).
    2:{ unfold oaddr. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
        rewrite Z2Nat.id by lia. rewrite Zplus_mod_idemp_l. f_equal. lia. }
    eexists. exact R.
Qed.

Lemma SPA_prune0 : ltac2:(tb__ "0|0|
S24S1dS12SeS0S2cQ40A1A1S2dS9S4S12A1S3aS1eR5A1A1S3S12R4A2A3S23S1cR7R6R4R3R2A6S23S1cR8S20R7R6A2R5R4R3A6F_;F_;Fw;Ftp;Frho;FT;FA;FJ;").
Proof.
  intros J A T rho tp w Hp Hsp. unfold prune0 in Hp.
  destruct (ss_objs (ax_S A)) as [|o rest] eqn:Eobjs; [discriminate|].
  destruct (ob_dflt o) eqn:Ed; try discriminate.
  destruct (sp_off (ax_S A) (ob_base o)) as [lo|]; [|discriminate].
  destruct (same_but_objs (ax_S A) (replace_obj_at (ax_S A) 0 (drop_cellsF (keep_cell lo) o))) eqn:Hsame; [|discriminate].
  injection Hp as <-.
  apply (SPA_replace_obj segs J rho A 0 o); [rewrite Eobjs; reflexivity | reflexivity | | exact Hsame | exact Hsp].
  intros ms _ Ho. apply obj_holds_drop_cells_unknown; assumption.
Qed.

Lemma SPA_trim : ltac2:(tb__ "0|0|
S24S1dS0ScA1SeS0S2cQ40A1A1S2dS28ScS10R3A1R4A3S9S1S27ScSfSdS1eR6A1A1A1R5A3S2A3S23S1cR8R7R5R4R3A6S23S1cR9S33R7R8A2R6R5R4A6F_;F_;F_;Fw;Ftp;Frho;FF;FA;FJ;").
Proof.
  intros J A F rho tp w HF Hb Hsp. unfold trim.
  pose proof (SPA_set_facts J A F rho tp w HF Hb Hsp) as H1.
  destruct (prune0 (ax_S (set_facts A F))) as [T|] eqn:Hp; [|exact H1].
  exact (SPA_prune0 J _ T rho tp w Hp H1).
Qed.

Lemma trim_next : ltac2:(tb__ "0|0|
S0ScA1S1dS9S29SdS1eS33R2R1A2A1A1SdS1eR1A1A1A3FA;FF;").
Proof.
  intros F A. unfold trim.
  destruct (prune0 (ax_S (set_facts A F))) as [T|] eqn:Hp; [|destruct A as [S X b]; reflexivity].
  unfold prune0 in Hp. destruct (ss_objs (ax_S (set_facts A F))) as [|o rest]; [discriminate|].
  destruct (ob_dflt o); try discriminate. destruct (sp_off (ax_S (set_facts A F)) (ob_base o)) as [lo|]; [|discriminate].
  destruct (same_but_objs _ _); [|discriminate]. injection Hp as <-.
  destruct A as [S X b]; reflexivity.
Qed.

Lemma trim_lenient : ltac2:(tb__ "0|0|
S0ScA1S1dS9S1S11S1eS33R2R1A2A1A1S11S1eR1A1A1A3FA;FF;").
Proof.
  intros F A. unfold trim.
  destruct (prune0 (ax_S (set_facts A F))) as [T|] eqn:Hp; [|destruct A as [S X b]; reflexivity].
  unfold prune0 in Hp. destruct (ss_objs (ax_S (set_facts A F))) as [|o rest]; [discriminate|].
  destruct (ob_dflt o); try discriminate. destruct (sp_off (ax_S (set_facts A F)) (ob_base o)) as [lo|]; [|discriminate].
  destruct (same_but_objs _ _); [|discriminate]. injection Hp as <-.
  destruct A as [S X b]; reflexivity.
Qed.

Lemma facts_in_hold : ltac2:(tb__ "0|0|
S24S0ScA1S1dSeS0S2cQ40A1A1S2dS9S1S39R5S1eR4A1A2S2A3S23S1cR7R5R4R3R2A6S28ScS10R5A1R7A3F_;F_;Fw;Ftp;Frho;FA;FF;FJ;").
Proof.
  intros J F A rho tp w Hin Hsp. pose proof (SPA_facts_hold segs J rho A tp w Hsp) as HF.
  apply Forall_forall. intros p Hp. pose proof (proj1 (forallb_forall _ _) Hin p Hp) as E. cbn beta in E.
  apply existsb_exists in E as (q & Hq & Eq). apply sprop_eqb_sound in Eq. subst q. exact (proj1 (Forall_forall _ _) HF _ Hq).
Qed.

Lemma seg0_run : ltac2:(tb__ "0|2|
S1dS1dS9S4S1dA1S3bR2A1S3S1dR1A2A3SaS9S4S0S1fA1M0A1S22S1cS37S36R3S2A5S3G0S7S1fS21R2S40A2S6S1fA1A3A2A3SaS31SdS1eR3A1A1SdS1eR2A1M1A1A2S9S1S11G1A1S5A3A2A2F_;FB;FA;").
Proof.
  intros A B H. unfold seg0 in H.
  destruct (sym_runA segs FUEL_T CUTS_FPS A true) as [ls|]; [|discriminate]. destruct ls as [|L ls']; [discriminate|]. destruct ls' as [|L2 ls'']; [|discriminate].
  destruct L as [S r]. cbn [la_reason la_state] in H. destruct r; try discriminate.
  destruct ((ss_next (ax_S A) <=? ss_next (ax_S S))%positive && negb (ss_lenient (ax_S S))) eqn:B0; [|discriminate].
  apply andb_prop in B0 as [B1 B2]. apply Pos.leb_le in B1. apply Bool.negb_true_iff in B2.
  injection H as <-. repeat split; assumption.
Qed.

Lemma runp_props : ltac2:(tb__ "0|3|
S0S0ScA1M0A1M1S1dS1dS9S4S1dA1S32R3R2A2S3S1dR1A2A3SaS31SdS1eR3A1M2A1SdS1eR2A1A1A2SbS9G1R4S6G0A1A3A1S9S1S11G2A1S5A3F_;A2F_;FB;FA;FFs;").
Proof.
  induction Fs as [|F Fs IH]; intros A B H; cbn [runp] in H.
  - injection H as <-. split; [lia | intros X; exfalso; exact (X eq_refl)].
  - destruct (seg0 (trim F A)) as [B1|] eqn:E1; [|discriminate].
    destruct (seg0_run _ B1 E1) as (_ & Hn1 & Hl1). rewrite trim_next in Hn1. destruct (IH B1 B H) as [Hn2 Hl2].
    split; [lia|]. intros _. destruct Fs as [|F' Fs']; [cbn [runp] in H; injection H as <-; exact Hl1 | apply Hl2; discriminate].
Qed.

Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S29SeSeS0ScA1S13R4R3R2A3S9S1S27ScSfR5A1R2A3S2A3S28ScS10R5A1M0R3A3S28ScG0R4A3F_;F_;F_;FF;Frho';Frho;Fn;").
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Lemma forallb_below_mono : ltac2:(tb__ "0|1|
S29S29S0ScA1S31R3R2A2S9S1S27ScSfR4A1M0R2A3S2A3S9S1S27ScG0R3A3S2A3F_;F_;FF;Fm;Fn;").
Proof.
  intros n m F Hle H. apply forallb_forall. intros p Hp. apply (sprop_below_mono n); [exact Hle | exact (proj1 (forallb_forall _ _) H p Hp)].
Qed.

Definition FsHold (rho : valuation) (Fs : list (list sprop)) : Prop := ltac2:(tb__ "0|1|
S28S0ScA1M0G0S28ScS10Vrho;A1R1A3LF;VFs;A3").
Definition FsBelow (n : positive) (Fs : list (list sprop)) : bool := ltac2:(tb__ "0|1|
S27S0ScA1M0G0S27ScSfVn;A1R1A3LF;VFs;A3").
Lemma FsHold_agree : ltac2:(tb__ "0|0|
S29SeSeS0S0ScA1A1S13R4R3R2A3S9S1S2aR5R2A2S2A3S2bR5R3A2S2bR5R4A2F_;F_;F_;FFs;Frho';Frho;Fn;").
Proof.
  intros n rho rho' Fs Hag Hb HF. unfold FsHold, FsBelow in *. apply Forall_forall. intros F HinF.
  eapply Forall_holds_agree; [exact Hag | exact (proj1 (forallb_forall _ _) Hb F HinF) | exact (proj1 (Forall_forall _ _) HF F HinF)].
Qed.
Lemma FsBelow_mono : ltac2:(tb__ "0|0|
S29S29S0S0ScA1A1S31R3R2A2S9S1S2aR4R2A2S2A3S9S1S2aR4R3A2S2A3F_;F_;FFs;Fm;Fn;").
Proof.
  intros n m Fs Hle H. unfold FsBelow in *. apply forallb_forall. intros F HinF. eapply forallb_below_mono; [exact Hle | exact (proj1 (forallb_forall _ _) H F HinF)].
Qed.

Lemma fs_ok_sound : ltac2:(tb__ "0|0|
S24S0S0ScA1A1S1dSeS0S2cQ40A1A1S2dS9S1S34R5S1eR4A1A2S2A3S23S1cR7R5R4R3R2A6SaS2bR5R7A2S9S1S2aSdS1eR6A1A1R7A2S2A3A2F_;F_;Fw;Ftp;Frho;FA;FFs;FJ;").
Proof.
  intros J Fs A rho tp w H Hsp. unfold fs_ok in H. split.
  - unfold FsHold. apply Forall_forall. intros F HinF. pose proof (proj1 (forallb_forall _ _) H F HinF) as X. apply andb_prop in X as [X _].
    exact (facts_in_hold J F A rho tp w X Hsp).
  - unfold FsBelow. apply forallb_forall. intros F HinF. pose proof (proj1 (forallb_forall _ _) H F HinF) as X. apply andb_prop in X as [_ X]. exact X.
Qed.
Lemma fs_ok_below : ltac2:(tb__ "0|0|
S0S0ScA1A1S12S9S1S34R2R1A2S2A3S9S1S2aSdR2A1R3A2S2A3F_;FS;FFs;").
Proof.
  intros Fs S H. unfold fs_ok in H. unfold FsBelow. apply forallb_forall. intros F HinF.
  pose proof (proj1 (forallb_forall _ _) H F HinF) as X. apply andb_prop in X as [_ X]. exact X.
Qed.

Section Run.
Variable ok : world -> Prop.
Variable J : jpredA.
Hypothesis Hst : ltac2:(tb__ "0|0|
S29S26S1cR1VJ;A3Flvl;").

Lemma runp_tr : ltac2:(tb__ "0|0|
S0S0ScA1A1S1dS1dSeS0S2cQ40A1A1S30S9S4S1dA1S32R6R5A2S3S1dR4A2A3S9S1S11S1eR6A1A1S5A3S25S1cVok;VJ;A3S2bR6R9A2S9S1S2aSdS1eR9A1A1RaA2S2A3SeS13SdS1eRbA1A1R9R1A3S2fS1cVok;S23S1cVJ;RbR2R9A5R8A4F_;Frho';S2fS1cVok;S23S1cVJ;RbR9R8A5R7A4F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FB;FA;FFs;").
Proof.
  induction Fs as [|F Fs IH]; intros A B rho tp Q H Hlen Hok HF Hb Hk; cbn [runp] in H.
  - injection H as <-. exact (Hk rho (agree_below_refl _ _)).
  - destruct (seg0 (trim F A)) as [B1|] eqn:E1; [|discriminate].
    destruct (seg0_run _ B1 E1) as (Hrun & Hn1 & Hl1). rewrite trim_next in Hn1.
    apply Forall_cons_iff in HF as [HF1 HF]. unfold FsBelow in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [Hb1 Hb].
    eapply triple_conseq with (P := SPA segs J (trim F A) rho tp); [intros w Hw; exact (SPA_trim J A F rho tp w HF1 Hb1 Hw) | intros w Hw; exact Hw |].
    eapply (runA_tr segs ok FUEL_T CUTS_FPS (trim F A) _ J rho tp); [exact Hrun | rewrite trim_lenient; exact Hlen | exact Hok | apply Hst |].
    intros L' rho1 [<-|[]] Hag1. cbn [la_state]. rewrite trim_next in Hag1.
    apply (IH B1 B rho1 tp Q H Hl1 Hok); [eapply FsHold_agree; eauto | eapply FsBelow_mono; eauto |].
    intros rho' Hag'. apply Hk. eapply agree_below_trans; [exact Hag1 | eapply agree_below_le; eauto].
Qed.

Lemma runp_etr : ltac2:(tb__ "0|0|
S0S0ScA1A1S1dS1dSeS0S2cQ40A1A1S2dOF_;S9S4S1dA1S32R6R5A2S3S1dR4A2A3S9S1S11S1eR6A1A1S5A3S2bR5R8A2S9S1S2aSdS1eR8A1A1R9A2S2A3SeS13SdS1eRaA1A1R8R1A3S2eS1cS23S1cVJ;RaR2R8A5R7A3F_;Frho';S2eS1cS23S1cVJ;RaR8R7A5R6A3F_;F_;F_;F_;F_;FQ;Ftp;Frho;FB;FA;FFs;").
Proof.
  induction Fs as [|F Fs IH]; intros A B rho tp Q H Hlen HF Hb Hk; cbn [runp] in H.
  - injection H as <-. exact (Hk rho (agree_below_refl _ _)).
  - destruct (seg0 (trim F A)) as [B1|] eqn:E1; [|discriminate].
    destruct (seg0_run _ B1 E1) as (Hrun & Hn1 & Hl1). rewrite trim_next in Hn1.
    apply Forall_cons_iff in HF as [HF1 HF]. unfold FsBelow in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [Hb1 Hb].
    eapply etriple_conseq with (P := SPA segs J (trim F A) rho tp); [intros w Hw; exact (SPA_trim J A F rho tp w HF1 Hb1 Hw) | intros w Hw; exact Hw |].
    eapply (erunA_tr segs FUEL_T CUTS_FPS (trim F A) _ J rho tp); [exact Hrun | rewrite trim_lenient; exact Hlen | apply Hst |].
    intros L' rho1 [<-|[]] Hag1. cbn [la_state]. rewrite trim_next in Hag1.
    apply (IH B1 B rho1 tp Q H Hl1); [eapply FsHold_agree; eauto | eapply FsBelow_mono; eauto |].
    intros rho' Hag'. apply Hk. eapply agree_below_trans; [exact Hag1 | eapply agree_below_le; eauto].
Qed.
End Run.
End Fps_run.

(* [comment removed for export] *)
Module Fps_facts.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "eval"; "holds"; "SAlu"; "SLit"; "SVar"; "SPNot"; "sprop"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "modulo"; "sub"; "@Corelib.Init.Logic"; "and"; "eq"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "GEU65"; "sX"; "ENDA"; "big_facts"; "@Corelib.Lists.ListDef"; "Forall"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundV SymSoundI SymSoundM SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform StrBytes MuslWL ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvFw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Icpt_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Icpt_strnlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Section ClassFacts2.
Variable r : valuation.
Hypothesis HFs : Forall (holds r) str_facts.
Hypothesis H140 : ltac2:(tb__ "0|0|
S10S1Q40A1S2Vr;P8cA2S2Vr;P10A2A3").
Let z := bv_unsigned (rw r 16).
Lemma str_factsZ : ltac2:(tb__ "0|5|
SfSbSaS0Q40M0S2Vr;P10A2A2Z10A2S0G0S2Vr;P11A2A2M1A2SfSbG1ScZ2M2Z3eA2M3A2SfSbSaS0G0S2Vr;P14A2A2G1A2S0G0S2Vr;P13A2A2M4A2SfSbG4ScG2Z28A2A2SfSbSaS0G0S2Vr;P12A2A2G4A2ScG2Z2fA2A2SfSbS0G0S3Vr;S15A2A2G3A2S11A2A2A2A2A2A2").
Proof.
  pose proof HFs as HF. unfold str_facts in HF.
  apply Forall_cons_iff in HF as [F2 HF]. apply Forall_cons_iff in HF as [F3 HF]. apply Forall_cons_iff in HF as [F4 HF].
  apply Forall_cons_iff in HF as [F6 HF]. apply Forall_cons_iff in HF as [F7 HF].
  apply Forall_cons_iff in HF as [F11 HF]. apply Forall_cons_iff in HF as [F12 HF]. apply Forall_cons_iff in HF as [F13 HF]. apply Forall_cons_iff in HF as [F14 HF].
  apply Forall_cons_iff in HF as [F15 HF]. apply Forall_cons_iff in HF as [F16 HF]. apply Forall_cons_iff in HF as [F17 HF].
  apply Forall_cons_iff in HF as [F18 HF]. apply Forall_cons_iff in HF as [F19 HF]. apply Forall_cons_iff in HF as [F21 HF]. apply Forall_cons_iff in HF as [F22 HF].
  apply Forall_cons_iff in HF as [F23 HF]. apply Forall_cons_iff in HF as [F24 HF].
  pose proof (urange (rw r 16)). pose proof (urange (rw r 17)). pose proof (urange (rw r 18)). pose proof (urange (rw r 19)). pose proof (urange (rw r 20)).
  unfold vXB, vXL, vXO in *.
  cbn [holds branch_taken eval] in F2, F3, F4, F11, F12, F13, F14, F15, F16, F17, F22, F24. rewrite lit_unsigned in F22. change (131071 mod 2 ^ 64) with 131071 in F22.
  cbn [holds] in F7. rewrite two62_eq in F7. change (bv_unsigned (eval r (SLit (2 ^ 62)))) with ((2 ^ 62) mod 2 ^ 64) in F7. change ((2 ^ 62) mod 2 ^ 64) with (2 ^ 62) in F7.
  rewrite lit_unsigned in F15. rewrite lit_unsigned in F17. change ((2 ^ 47 - 64) mod 2 ^ 64) with (2 ^ 47 - 64) in F17.
  rewrite add_lit_val in F2. change (snorm 8) with 8 in F2.
  rewrite add_lit_val in F24. change (snorm 16) with 16 in F24.
  rewrite lit_unsigned in F3. change (8 mod 2 ^ 64) with 8 in F3.
  rewrite two62_eq, lit_unsigned in F4. change ((2 ^ 62) mod 2 ^ 64) with (2 ^ 62) in F4.
  rewrite add_val in F11. rewrite lit_unsigned in F14. change ((2 ^ 40) mod 2 ^ 64) with (2 ^ 40) in F14.
  rewrite add_val, lit_unsigned in F16. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47) in F16.
  assert (Ea : (bv_unsigned (rw r 16) + 8) mod 2 ^ 64 = bv_unsigned (rw r 16) + 8).
  { destruct (Z_lt_le_dec (bv_unsigned (rw r 16) + 8) (2 ^ 64)); [apply Z.mod_small; lia |].
    exfalso. replace (bv_unsigned (rw r 16) + 8) with ((bv_unsigned (rw r 16) + 8 - 2 ^ 64) + 1 * 2 ^ 64) in F2 by lia.
    rewrite Z_mod_plus_full, Z.mod_small in F2 by lia. lia. }
  rewrite Ea in F2.
  assert (Ex : (bv_unsigned (rw r 16) + 16) mod 2 ^ 64 = bv_unsigned (rw r 16) + 16).
  { destruct (Z_lt_le_dec (bv_unsigned (rw r 16) + 16) (2 ^ 64)); [apply Z.mod_small; lia |].
    exfalso. replace (bv_unsigned (rw r 16) + 16) with ((bv_unsigned (rw r 16) + 16 - 2 ^ 64) + 1 * 2 ^ 64) in F24 by lia.
    rewrite Z_mod_plus_full, Z.mod_small in F24 by lia. lia. }
  rewrite Ex in F24.
  assert (Eb : (bv_unsigned (rw r 20) + bv_unsigned (rw r 17)) mod 2 ^ 64 = bv_unsigned (rw r 20) + bv_unsigned (rw r 17)) by (apply Z.mod_small; lia).
  rewrite Eb in F11.
  assert (Ec : (bv_unsigned (rw r 18) + bv_unsigned (rw r 19)) mod 2 ^ 64 = bv_unsigned (rw r 18) + bv_unsigned (rw r 19)) by (apply Z.mod_small; lia).
  rewrite Ec in F16.
  repeat split; lia.
Qed.
Lemma U_sX' : ltac2:(tb__ "0|1|
S10S12S0Q40M0S3Vr;S15A2A2SaS0G0S2Vr;P12A2A2S0G0S2Vr;P14A2A2A2A3").
Proof.
  destruct str_factsZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 17)).
  unfold sX, vXB, vXO. apply (U_add2 r (SVar 18) (SVar 20)); [reflexivity | reflexivity | lia].
Qed.
Lemma U_z1' : ltac2:(tb__ "0|1|
S10S12S0Q40S3Vr;S5S13S7P8cA1S6Z1M0A1A3A2A2SaVz;G0A2A3").
Proof. pose proof (urange (rw r 16)). destruct str_factsZ as (Z1 & Z2 & _). apply (U_addc r (SVar 140) 1 z); [cbn [eval]; rewrite H140; reflexivity | lia | lia]. Qed.
Lemma U_ENDA' : ltac2:(tb__ "0|1|
S10S12S0Q40M0S3Vr;S16A2A2SaSaS0G0S2Vr;P12A2A2S0G0S2Vr;P14A2A2A2Vz;A2A3").
Proof.
  destruct str_factsZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 17)). pose proof (urange (rw r 16)).
  assert (A2 : bv_unsigned (eval r (SAlu ALU_ADD sX (SAlu ALU_ADD (SVar 140) (SLit 1)))) = bv_unsigned (rw r 18) + bv_unsigned (rw r 20) + (z + 1)).
  { apply (U_add2 r _ _ _ _ U_sX' U_z1'). lia. }
  unfold ENDA. rewrite (U_addc r _ (-1) _ A2); lia.
Qed.
Lemma post_facts_hold' : Forall (holds r) post_facts.
Proof.
  destruct str_factsZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 16)).
  unfold post_facts. constructor; [|constructor; [|constructor]]; cbn [holds].
  - change (eval r vXB) with (rw r 18). rewrite U_ENDA'. lia.
  - rewrite (U_addc r ENDA 1 _ U_ENDA') by lia. unfold vXB, vXL. pose proof (urange (rw r 19)).
    rewrite (U_add2 r (SVar 18) (SVar 19) (bv_unsigned (rw r 18)) (bv_unsigned (rw r 19)) eq_refl eq_refl) by lia. lia.
Qed.
Lemma U_m64' : ltac2:(tb__ "0|1|
S10S12S0Q40S3Vr;S5S13S7P8cA1S6N40A1A3A2A2SdSeVz;Z40M0A2ScZ2G0A2A2A3").
Proof. cbn [eval]. rewrite add_lit_val, H140. change (snorm (-64)) with (-64). reflexivity. Qed.
Lemma GEU65_S' : ltac2:(tb__ "0|0|
SbSaVz;Z1A2Z40A2S4Vr;S8S14A1A2F_;").
Proof.
  intros Hz. pose proof (urange (rw r 16)). unfold GEU65. cbn [holds branch_taken]. unfold bv_ltu. rewrite U_m64', (U_lit64 r 18446744073709551551) by lia.
  replace ((z - 64) mod 2 ^ 64) with (z - 64 + 2 ^ 64) by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small; lia).
  destruct (Z.ltb_spec 18446744073709551551 (z - 64 + 2 ^ 64)); [cbn; congruence | lia].
Qed.
Lemma GEU65_B' : ltac2:(tb__ "0|0|
SbZ41SaVz;Z1A2A2S4Vr;S14A2F_;").
Proof.
  intros Hz. destruct str_factsZ as (Z1 & Z2 & _). pose proof (urange (rw r 16)). unfold GEU65. cbn [holds branch_taken]. unfold bv_ltu. rewrite U_m64', (U_lit64 r 18446744073709551551) by lia.
  rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec 18446744073709551551 (z - 64)); [lia | reflexivity].
Qed.
Lemma big_facts_hold' : ltac2:(tb__ "0|0|
SbZ41SaVz;Z1A2A2S18S9S4Vr;A1S17A3F_;").
Proof.
  intros Hz. destruct str_factsZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 16)). pose proof (urange (rw r 20)).
  pose proof U_z1' as U141. change (SAlu ALU_ADD (SVar 140) (SLit 1)) with N1 in U141.
  unfold big_facts. apply Forall_app. split.
  2:{ apply (rip8_facts_hold r N1 (z + 1) U141); lia. }
  constructor; [|constructor; [|constructor; [|constructor]]]; cbn [holds]; unfold vXO, vXL.
  - pose proof (urange (rw r 19)). rewrite (U_add2 r (SVar 20) _ (bv_unsigned (rw r 20)) (z + 1) eq_refl U141) by lia. change (eval r (SVar 19)) with (rw r 19). lia.
  - rewrite U141. change (eval r (SVar 19)) with (rw r 19). lia.
  - rewrite U141, (U_lit64 r 1) by lia. lia.
Qed.
End ClassFacts2.
End Fps_facts.

(* [comment removed for export] *)
Module FpsC_st.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "sym_runA"; "la_state"; "mkLeafA"; "ax_setS"; "axwf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "Some"; "option"; "list"; "false"; "cons"; "nil"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sprop"; "ss_lenient"; "SVar"; "sstate"; "SPEq"; "sobj"; "ss_facts"; "sv"; "SLit"; "sprop_eqb"; "ss_pc"; "swf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st"; "E4S"; "Pre"; "E2"; "E6bS"; "E6sS"; "s_isl"; "E1"; "E4"; "T3"; "T7b"; "T7s"; "s_sib"; "s_sis"; "E6b"; "E6s"; "R_isl"; "R_rip"; "R_sib"; "R_sis"; "T3B"; "T3S"; "T5"; "T5F"; "s_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "CUTS_FPS"; "facts_fps"; "FSB"; "FSS"; "fs_ok"; "runp"; "zvar"; "XF6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st"; "Pre_si"; "P_si"; "Posts_si"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen"; "Pre_isl"; "P_isl"; "Posts_isl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.Lists.List"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsB"; "factsS"; "sX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates"; "obindW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen.ISLAddr"; "isl_entry"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition Pre : axst := Pre_fps FMT_COPEN 0x1ee40 0x80.

Definition run1__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S3aU7d0S3bS23SbA5").
Local Strategy expand [run1__R].
Definition E1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => lf0 Pre (ro1__) 0) run1__R).
Definition run2__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S3aUbb8S3bS28SbA5").
Local Strategy expand [run2__R].
Definition E2 := Eval vm_compute in ((fun ro2__ : option (list leafA) => lf0 E1 (ro2__) 0) run2__R).
Definition s_isl := Eval vm_compute in ((16%positive, SVar 16) :: infer_sub 10 (ax_S E2) (ax_S Pre_isl)).
Definition R_isl := Eval vm_compute in match entails_frA E2 Pre_isl s_isl with Some R => R | None => [] end.
Definition T3 := Eval vm_compute in import_postA s_isl Pre_isl P_isl E2 R_isl.

Definition T3S : axst := ltac2:(tb__ "0|0|
S52S12S14S56S3cA3S2aA2").
Definition E6s := Eval vm_compute in match runp FSS T3S with Some A => A | None => T3S end.
Definition E6sS := Eval vm_compute in match apply_axforms E6s [AXSplit 1 (SLit (-1024))] with Some A => A | None => E6s end.
Definition s_sis := Eval vm_compute in ([(16%positive, SVar 16); (17%positive, SVar 17); (20%positive, SVar 20)] ++ infer_sub 10 (ax_S E6sS) (ax_S Pre_si)).
Definition R_sis := Eval vm_compute in match entails_frA E6sS Pre_si s_sis with Some R => R | None => [] end.
Definition T7s := Eval vm_compute in import_postA s_sis Pre_si P_si E6sS R_sis.

Definition T3B : axst := ltac2:(tb__ "0|0|
S52S12S14S55S3cA3S2aA2").
Definition run3b__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S3aUbb8S3bS35SbA5").
Local Strategy expand [run3b__R].
Definition E4 := Eval vm_compute in ((fun ro3__ : option (list leafA) => lf0 T3B (ro3__) 0) run3b__R).
Definition E4S := Eval vm_compute in
  match split_obj_at (ax_S E4) 1 (SLit (-2352)) with Some S1 =>
  match split_obj_at S1 1 (SLit (-2432)) with Some S2 => ax_setS E4 S2 | None => E4 end | None => E4 end.
Definition s_rip := Eval vm_compute in ((16%positive, vXL8) :: infer_sub 10 (ax_S E4S) (ax_S Pre_rip)).
Definition R_rip := Eval vm_compute in match entails_frA E4S Pre_rip s_rip with Some R => R | None => [] end.
Definition T5 := Eval vm_compute in import_postA s_rip Pre_rip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.P_ret E4S R_rip.
Definition T5F : axst := ltac2:(tb__ "0|0|
S52S10S14S18S16P8cA1S16P10A1A2S12S14S55S3cA3A3S37A2").
Definition E6b := Eval vm_compute in match runp FSB T5F with Some A => A | None => T5F end.
Definition E6bS := Eval vm_compute in match apply_axforms E6b XF6 with Some A => A | None => E6b end.
Definition s_sib := Eval vm_compute in ([(16%positive, SVar 16); (17%positive, SVar 17); (20%positive, SVar 20)] ++ infer_sub 10 (ax_S E6bS) (ax_S Pre_si)).
Definition R_sib := Eval vm_compute in match entails_frA E6bS Pre_si s_sib with Some R => R | None => [] end.
Definition T7b := Eval vm_compute in import_postA s_sib Pre_si P_si E6bS R_sib.

Lemma pre_wf : ltac2:(tb__ "0|0|
S1S0SaS9S23A1SbA3S0SaS1fS2S23A1A1SbA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma pre_facts : ltac2:(tb__ "0|0|
S0SeS14A1S1aS2S23A1A1S3cA3"). Proof. reflexivity. Qed.
Lemma xs4 : ltac2:(tb__ "0|0|
S0S3S8S29S2S22A1A2S22A3"). Proof. reflexivity. Qed.
Lemma lenT7 : ltac2:(tb__ "0|0|
S1S0SaS15S2S2cA1A1SfA3S0SaS15S2S2bA1A1SfA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma run1 : ltac2:(tb__ "0|1|
S0SdSeS4A1M0A1S5S3aU7d0S3bS23SbA5ScG0S10S4S7S28S51A2S11S4A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run1__R <: run1__R = Some [mkLeafA E1 RsCut]). Qed.
Lemma run2 : ltac2:(tb__ "0|1|
S0SdSeS4A1M0A1S5S3aUbb8S3bS28SbA5ScG0S10S4S7S24S51A2S11S4A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run2__R <: run2__R = Some [mkLeafA E2 RsCut]). Qed.
Lemma efr_isl : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS24S4eS27A3ScG0S31A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_isl)). Qed.
Lemma chk_isl : ltac2:(tb__ "0|0|
S0SaS4aS24S4eS27S31S48S4S3S6S50A4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_isl : ltac2:(tb__ "0|0|
S0S3S4cS27S4eS4fS24S31A5S2aA3"). Proof. vm_cast_no_check (eq_refl T3). Qed.
Lemma fsS : ltac2:(tb__ "0|0|
S0SaS3fS3eS2S36A1A2SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run3s : ltac2:(tb__ "0|0|
S0SdS3A1S40S3eS36A2ScS3S30A2A3"). Proof. vm_cast_no_check (eq_refl (Some E6s)). Qed.
Lemma xf6s : ltac2:(tb__ "0|0|
S0SdS3A1S59S30S10S5aS5bU1S1cN400A1A2S11S5aA1A3A2ScS3S26A2A3"). Proof. vm_cast_no_check (eq_refl (Some E6sS)). Qed.
Lemma efr_sis : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS26S43S2eA3ScG0S34A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_sis)). Qed.
Lemma chk_sis : ltac2:(tb__ "0|0|
S0SaS4aS26S43S2eS34S48S4S3S6S45A4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_sis : ltac2:(tb__ "0|0|
S0S3S4cS2eS43S44S26S34A5S2cA3"). Proof. vm_cast_no_check (eq_refl T7s). Qed.
Lemma run3b : ltac2:(tb__ "0|1|
S0SdSeS4A1M0A1S5S3aUbb8S3bS35SbA5ScG0S10S4S7S29S51A2S11S4A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run3b__R <: run3b__R = Some [mkLeafA E4 RsCut]). Qed.
Lemma split4 : ltac2:(tb__ "0|1|
S0SdS17A1S5cS17S17S58S2S29A1U1M0S1cN930A1A3S17S58R1G0S1cN980A1A3LS1;A4ScS17S2S22A1A2A3").
Proof. vm_cast_no_check (eq_refl (Some (ax_S E4S))). Qed.
Lemma efr_rip : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS22S4dS39A3ScG0S32A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_rip)). Qed.
Lemma chk_rip : ltac2:(tb__ "0|0|
S0SaS4aS22S4dS39S32S48S4S3S6S5eA4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_rip : ltac2:(tb__ "0|0|
S0S3S4cS39S4dS5dS22S32A5S37A3"). Proof. vm_cast_no_check (eq_refl T5). Qed.
Lemma fsB : ltac2:(tb__ "0|0|
S0SaS3fS3dS2S38A1A2SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run5 : ltac2:(tb__ "0|0|
S0SdS3A1S40S3dS38A2ScS3S2fA2A3"). Proof. vm_cast_no_check (eq_refl (Some E6b)). Qed.
Lemma xf6b : ltac2:(tb__ "0|0|
S0SdS3A1S59S2fS42A2ScS3S25A2A3"). Proof. vm_cast_no_check (eq_refl (Some E6bS)). Qed.
Lemma efr_sib : ltac2:(tb__ "0|1|
S0SdSeS19A1M0A1S4bS25S43S2dA3ScG0S33A2A3"). Proof. vm_cast_no_check (eq_refl (Some R_sib)). Qed.
Lemma chk_sib : ltac2:(tb__ "0|0|
S0SaS4aS25S43S2dS33S48S4S3S6S45A4A5SbA3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma imp_sib : ltac2:(tb__ "0|0|
S0S3S4cS2dS43S44S25S33A5S2bA3"). Proof. vm_cast_no_check (eq_refl T7b). Qed.

Lemma shapes : ltac2:(tb__ "0|10|
S1S0SaS15S2S23A1M0A1SfA3S1S0S20S13G0A1S53A3S1S0S20S13S2S28A1M1A1S53A3S1S0SaS15G1A1SfA3S1S0S21S1eG1A1S5fA3S1S0S20S13S2S24A1A1S53A3S1S0S1bS49S27P10M2A2S16G2A1M3A3S1S0S1bS49S27PcA2S57A3S1S0S20S13S2S2aA1M4A1P8dM5A3S1S0SaS54S14S1dS18S16P8cA1G3A2A1S1aG4A1A3SbA3S1S0SaS15S2S36A1A1SfA3S1S0SaS15S2S35A1A1SfA3S1S0S20S13S2S30A1A1M6S13S2S26A1A1A3S1S0SaS47G5G6A2SbA3S1S0S1bS49S2eG2A2G3A3S1S0S20S13S2S29A1A1M7S13S2S22A1A1A3S1S0SaS47G5G7A2SbA3S1S0S20S13S2S37A1A1M8S46G7P28M9A2A3S1S0SaS15S2S38A1A1SfA3S1S0S20S13S2S2fA1A1MaS13S2S25A1A1A3S1S0SaS47G8GaA2SbA3S1S0S1bS49S2dG2A2G3A3S1S0S20S41S2cA1MbS46G6G9A2A3S1S0S20S13S2S2cA1McA1S46G6P29MdA2A3S1S0S20S41S2bA1MeS46GaG9A2A3S1S0S20S13S2S2bA1MfA1S46GaGdA2A3S1S0SaS54S14S1dS18S16GbA1G3A2A1S1aGcA1A3SbA3S0SaS54S14S1dS18S16GeA1G3A2A1S1aGfA1A3SbA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End FpsC_st.

