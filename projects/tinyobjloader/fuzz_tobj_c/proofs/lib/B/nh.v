(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc nd np no.

(* [comment removed for export] *)
Module Icpt_strnlen_st.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "true"; "bool"; "nil"; "Some"; "option"; "list"; "false"; "pair"; "app"; "prod"; "None"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "sym_runA"; "mkLeafA"; "axwf"; "entailsA"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sv"; "ss_next"; "sprop"; "sobj"; "SLit"; "ss_lenient"; "sstate"; "SPEq"; "sprop_below"; "FcsrFrm0"; "SAlu"; "mkSS"; "swf"; "DUnknown"; "SPBranch"; "SPUle"; "cell"; "mkObj"; "sprop_eqb"; "ss_facts"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXRebase"; "AXMerge"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st"; "CUTS_SI"; "FUEL_SI"; "facts_si"; "E_callS"; "E_ripS"; "P_si"; "Pre_si"; "s_call"; "D_SI"; "E_call"; "E_rip"; "G_B"; "G_S"; "R_B"; "R_S"; "R_call"; "R_rip"; "T_B"; "T_S"; "T_rip"; "T_ripF"; "s_rip"; "F_SI"; "T_imp"; "X_si"; "objs_si"; "si_ret"; "sp_B"; "sp_S"; "O_winI"; "XB4"; "XS4"; "si_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "RsSymJump"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st"; "Pre_sn"; "P_sn"; "Posts_sn"; "sn_entry"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "O_cfsl"; "O_realmc"; "O_realsn"; "O_strS"; "factsB"; "factsS"; "facts_mci"; "sX"; "vXB"; "vXL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "O_rtc2"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition si_entry : Z := 0x4d5d4.
Definition si_ret : Z := 0x4d6c0.
Definition F_SI : Z := 2144.
Definition D_SI : Z := D_SN + F_SI.
Definition O_winI : sobj := ltac2:(tb__ "0|0|
S29S17PaA1S1cS68S3fA1A1S1cZ0A1S4S28A1S25A5").
Definition facts_si : list sprop := ltac2:(tb__ "0|0|
SaS1aS0S1aS27S1cS67S67S67S35Z1000A2Z20A2S4dA2A1S17PaA1A2S0S1aS26S6bS22S6aS17P10A1S1cZ1A1A3S17PeA1A3S4S1aA1A3A3S78A3").
Definition X_si : list (sv * sv) := ltac2:(tb__ "0|1|
S0SbS18S18A2M0S9S18S18S7aS7bA4S0G0S9S18S18S22S6aS17PaA1S1cS68S3fA1A1A3S1cS3fA1A4S4G0A1A3A3").
Definition objs_si : list sobj := ltac2:(tb__ "0|0|
SaS1bS0S1bS54S0S1bS75S0S1bS7cS0S1bS7dS0S1bS73S0S1bS74S0S1bS72S4S1bA1A3A3A3A3A3A3A3S36A3").

Definition Pre_si : axst := ltac2:(tb__ "0|1|
S34S23S57S5aS5cS0SbS1S18A2M0S9S1S18UaS79A4S0G0S9S1S18UbS17PeA1A4S0G0S9S1S18UcS17PdA1A4S4G0A1A3A3A3A2S59S21ScS18A1S50S39S58S8A9S4fA2").
Definition CUTS_SI : ltac2:(tb__ "0|0|
S7S2dA1") := ltac2:(tb__ "0|0|
S0S2dS65S0S2dS7fS0S2dS51S4S2dA1A3A3A3").
Definition FUEL_SI : nat := 300%nat.

Definition si_run_call__R : option (list leafA) := ltac2:(tb__ "0|0|
S12S33S38S37S3dS2A5").
Local Strategy expand [si_run_call__R].
Definition E_call : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => lf0 Pre_si (ro1__) 0) si_run_call__R).
Definition E_callS : axst := Eval vm_compute in match split_obj_at (ax_S E_call) 0 (SLit (- F_SI)) with Some S' => ax_setS E_call S' | None => E_call end.
Definition s_call : wsub := Eval vm_compute in infer_sub 10 (ax_S E_callS) (ax_S Pre_sn).
Definition R_call : list sobj := Eval vm_compute in match entails_frA E_callS Pre_sn s_call with Some R => R | None => [] end.
Definition T_imp : axst := Eval vm_compute in import_postA s_call Pre_sn P_sn E_callS R_call.
Definition T_impF : axst := ax_add_facts facts_si T_imp.

Definition T_S : axst := ax_add_facts factsS T_impF.
Definition T_B : axst := ax_add_facts factsB T_impF.

Definition si_run_S__R : option (list leafA) := ltac2:(tb__ "0|0|
S12S33S38S37S49S2A5").
Local Strategy expand [si_run_S__R].
Definition R_S : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => lf0 T_S (ro2__) 0) si_run_S__R).

Definition si_run_B__R : option (list leafA) := ltac2:(tb__ "0|0|
S12S33S38S37S48S2A5").
Local Strategy expand [si_run_B__R].
Definition E_rip : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => lf0 T_B (ro3__) 0) si_run_B__R).
Definition E_ripS : axst := Eval vm_compute in match split_obj_at (ax_S E_rip) 0 (SLit (-80)) with Some S' => ax_setS E_rip S' | None => E_rip end.
Definition s_rip : wsub := Eval vm_compute in ((16%positive, vXL8) :: infer_sub 10 (ax_S E_ripS) (ax_S Pre_rip)).
Definition R_rip : list sobj := Eval vm_compute in match entails_frA E_ripS Pre_rip s_rip with Some R => R | None => [] end.
Definition T_rip : axst := Eval vm_compute in import_postA s_rip Pre_rip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.P_ret E_ripS R_rip.
Definition T_ripF : axst := ltac2:(tb__ "0|0|
S81S0S1aS1fS17P8cA1S17P10A1A2S39A3S4aA2").
Definition si_run_B2__R : option (list leafA) := ltac2:(tb__ "0|0|
S12S33S38S37S4bS2A5").
Local Strategy expand [si_run_B2__R].
Definition R_B : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => lf0 T_ripF (ro4__) 0) si_run_B2__R).

Definition XS4 : list axform := ltac2:(tb__ "0|1|
S0S2eS2fU0M0A1S0S2eS31S0S1G0S0S1U7S0S1U1S0S1U2S0S1U3S0S1U4S0S1U8S0S1U9S0S1U5S0S1U6S4S1A1A3A3A3A3A3A3A3A3A3A3A1S0S2eS30G0A1S4S2eA1A3A3A3").
Definition XB4 : list axform := ltac2:(tb__ "0|3|
S0S2eS2fU0M0A1S0S2eS2fU4M1A1S0S2eS31S0S1G1S0S1G0S0S1U8S0S1U5S0S1U6S0S1U1S0S1U7S0S1U9S0S1UaS0S1U2S0S1U3S4S1A1A3A3A3A3A3A3A3A3A3A3A3A1S0S2eS30G0A1M2S0S2eG2S4S2eA1A3A3A3A3A3").
Definition G_S : axst := Eval vm_compute in match apply_axforms R_S XS4 with Some A => A | None => R_S end.
Definition G_B : axst := Eval vm_compute in match apply_axforms R_B XB4 with Some A => A | None => R_B end.
Definition P_si0 : axst := ltac2:(tb__ "0|1|
S34S23S51S5aS5bS58A1S0SbS1S18A2M0S9S1S18UaS17P8cA1A4S4G0A1A3A2S59S21ScS18A1S50S39P8dS8A9S4fA2").
Definition P_si : axst := ax_add_facts F_post P_si0.
Definition Posts_si : list leafA := ltac2:(tb__ "0|0|
S0S10S13S3cS5eA2S4S10A1A3").
Definition sp_S : wsub := Eval vm_compute in infer_sub NF (ax_S G_S) (ax_S P_si0).
Definition sp_B : wsub := Eval vm_compute in infer_sub NF (ax_S G_B) (ax_S P_si0).

Lemma si_wf : ltac2:(tb__ "0|0|
SeSdS3S14S3dA1S2A3SeSdS3S24SfS3dA1A1S2A3SeSdS3S14S3cA1S2A3SdS3S24SfS3cA1A1S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma si_run_call : ltac2:(tb__ "0|1|
SdS6S7S10A1M0A1S12S33S38S37S3dS2A5S5G0S0S10S13S40S5dA2S4S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) si_run_call__R <: si_run_call__R = Some [mkLeafA E_call RsCut]). Qed.
Lemma si_split_call : ltac2:(tb__ "0|0|
SdS6S1eA1S6eSfS40A1U0S1cS68S4dA1A1A3S5S1eSfS3aA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_efr_call : ltac2:(tb__ "0|1|
SdS6S7S1bA1M0A1S70S3aS62S3eA3S5G0S46A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_chk_call : ltac2:(tb__ "0|0|
SdS3S6fS3aS62S3eS46S69S10S11S16S64A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_imp_call : ltac2:(tb__ "0|0|
SdS11S71S3eS62S63S3aS46A5S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_run_S : ltac2:(tb__ "0|1|
SdS6S7S10A1M0A1S12S33S38S37S49S2A5S5G0S0S10S13S45S5dA2S4S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) si_run_S__R <: si_run_S__R = Some [mkLeafA R_S RsCut]). Qed.
Lemma si_run_B : ltac2:(tb__ "0|1|
SdS6S7S10A1M0A1S12S33S38S37S48S2A5S5G0S0S10S13S41S5dA2S4S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) si_run_B__R <: si_run_B__R = Some [mkLeafA E_rip RsCut]). Qed.
Lemma si_split_rip : ltac2:(tb__ "0|0|
SdS6S1eA1S6eSfS41A1U0S1cN50A1A3S5S1eSfS3bA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_efr_rip : ltac2:(tb__ "0|1|
SdS6S7S1bA1M0A1S70S3bS61S4cA3S5G0S47A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_chk_rip : ltac2:(tb__ "0|0|
SdS3S6fS3bS61S4cS47S69S10S11S16S80A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_imp_rip : ltac2:(tb__ "0|0|
SdS11S71S4cS61S7eS3bS47A5S4aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_run_B2 : ltac2:(tb__ "0|1|
SdS6S7S10A1M0A1S12S33S38S37S4bS2A5S5G0S0S10S13S44S5dA2S4S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) si_run_B2__R <: si_run_B2__R = Some [mkLeafA R_B RsCut]). Qed.
Lemma si_xf_S : ltac2:(tb__ "0|0|
SdS6S11A1S32S45S56A2S5S11S43A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_xf_B : ltac2:(tb__ "0|0|
SdS6S11A1S32S44S55A2S5S11S42A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_ent_S : ltac2:(tb__ "0|0|
SdS3S15S43S3cS53A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_ent_B : ltac2:(tb__ "0|0|
SdS3S15S42S3cS52A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_ids : ltac2:(tb__ "0|0|
SeSdS3S6cS53S58A2S2A3SdS3S6cS52S58A2S2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma si_shape_call : ltac2:(tb__ "0|2|
SeSdS3S1dSfS3dA1M0A1S8A3SeSdS2cS19G0A1S58A3SeSdS2cS19SfS40A1A1S58A3SeSdS2cS19SfS3aA1A1S58A3SeSdS18S6dS3eP10M1A2S17G1A1A3SdS3S5fS1aS20S58A1S39A3S2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma si_shape_imp : ltac2:(tb__ "0|5|
SeSdS2cS19SfS4eA1M0A1P8dM1A3SeSdS3S1dSfS49A1M2A1S8A3SeSdS2cS19G2A1G1A3SeSdS3S1dSfS48A1M3A1S8A3SeSdS2cS19G3A1G1A3SeSdS3S60S1aS2aS1fS17P8cA1S17P10A1A2A1S2bG0A1A3S2A3SeSdS3S5fS1aS20G1A1M4SaS1aS77S39A3A3S2A3SdS3S5fS1aG4SaS1aS76S39A3A3S2A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma si_shape_rip : ltac2:(tb__ "0|3|
SeSdS2cS19SfS3bA1A1S19SfS41A1A1M0A3SeSdS2cS19SfS4aA1A1Pb5M1A3SeSdS3S1dSfS4bA1M2A1S8A3SeSdS2cS19G2A1G1A3SeSdS3S66P8dG0A2S2A3SdS3S5fS1aS20G1A1S0S1aS1fS17P8cA1S17P10A1A2S39A3A3S2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma si_shape_ret : ltac2:(tb__ "0|2|
SeSdS2cS19SfS45A1A1M0S19SfS43A1A1A3SeSdS2cS19SfS44A1A1M1S19SfS42A1A1A3SeSdS3S66P8dG0A2S2A3SdS3S66Pb5G1A2S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Icpt_strnlen_st.

(* [comment removed for export] *)
Module Asan_memcpy48.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "nat"; "bool"; "pair"; "true"; "None"; "false"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "cell"; "sprop"; "sobj"; "SLit"; "sv"; "valuation"; "DUnknown"; "FcsrFrm0"; "SPAlign"; "SPUle"; "agree_below"; "mkObj"; "mkSS"; "sprop_below"; "ss_next"; "mkCell"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Asan_memcpy48"; "c4x"; "Pre48_0"; "Posts48"; "Pre48_1"; "Pre48_2"; "base48"; "FUEL48"; "P48"; "cuts48"; "objs48"; "vcuts48"; "O_dst'"; "O_src'"; "al48_cells4"; "exits48"; "vexits48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "NPOST"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "withGA"; "check_cfgA"; "vna_state"; "@Corelib.Init.Logic"; "eq"; "or"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "xor_facts"; "dst"; "X_mc"; "ord1"; "ord2"; "src"; "O_real"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "vN"; "O_rtc2"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface"; "al48_cells"; "thunk_alloc48"; "thunk_calloc48"; "thunk_free48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memcpy.AMCAddr"; "mc_entry"; "mc_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memcpy"; "O_cstk"; "O_frame"; "O_rest"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Asan_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations. Import RegionAddr. Import AMCAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition O_dst' (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S19S46S11Z0A1S4dVcs;S14A5").
Definition O_src' (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S19S4aS11Z0A1S4dVcs;S14A5").
Definition objs48 (fr dcs scs : list cell) : list sobj := ltac2:(tb__ "0|0|
SaS10S0S10S60Vfr;A1S0S10S5fS0S10S61S0S10S2aVdcs;A1S0S10S2bVscs;A1S0S10S4cS0S10S4eS0S10S4bS1S10A1A3A3A3A3A3A3A3A3SdA3").

Definition PIN48 : list sprop := ltac2:(tb__ "0|2|
S0SfS17S4dS11Z30A1M0A2S0SfS17G0S4dA2S0SfS16P11Z3M1A2S0SfS16P35G1A2S1SfA1A3A3A3A3").
Definition base48 : list sprop := PIN48 ++ base_mc.

Definition c4x (o : Z) (v : Z) : cell := ltac2:(tb__ "0|0|
S1dS11Vo;A1Z4S11Vv;A1A3").
Definition al48_cells4 : list cell := ltac2:(tb__ "0|1|
S0SeS1fZ2cZ0M0A2S0SeS1fZ28G0A2S0SeS1fZ24G0A2S0SeS1fZ20G0A2S0SeS1fZ1cG0A2S0SeS1fZ18S53A2S0SeS1fZ14G0A2S0SeS1fZ10G0A2S0SeS1fZcG0A2S0SeS1fZ8S52A2S0SeS1fZ4G0A2S0SeS1fG0S51A2S1SeA1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition Pre48_0 : axst := ltac2:(tb__ "0|2|
ScS1aS5dS31S34S0S9S3S12A2M0S5S3S12UaS46A4S0G0S5S3S12UbS4aA4S0G0S5S3S12UcS11Z30A1A4S1G0A1A3A3A3A2S30S15S7S12A1S28S1SeA1M1G1S50A3S24S2fS8A9S47A2").
Definition Pre48_1 : axst := ltac2:(tb__ "0|0|
S3aS0SfS48S45A3S20A2").
Definition Pre48_2 : axst := ltac2:(tb__ "0|0|
S3aS0SfS49S45A3S20A2").
Definition P48 : axst := ltac2:(tb__ "0|1|
ScS1aS5eS31S33S2fA1S0S9S3S12A2M0S5S3S12UaS46A4S1G0A1A3A2S30S15S7S12A1S28S1SeA1S2cS50A3S24S32S8A9S47A2").
Definition Posts48 : list leafA := ltac2:(tb__ "0|0|
S0S43S44S26S62A2S1S43A1A3").

Definition cuts48 : list axst := ltac2:(tb__ "0|0|
S0S41S22S0S41S23S1S41A1A3A3").
Definition exits48 : list axst := [P48].
Definition FUEL48 : nat := 1500%nat.
Definition vcuts48 : list vnodeA := ltac2:(tb__ "0|2|
S0S38S39S22Z1M0S11Z0A1M1A3S0S38S39S23G0G1A3S1S38A1A3A3").
Definition vexits48 : list vnodeA := ltac2:(tb__ "0|0|
S0S38S39S26Z0S11Z1A1A3S1S38A1A3").

Lemma echeck48 : ltac2:(tb__ "0|0|
S3eS4S63SbS25S1S4fA1S2fS29S2eA6S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check48 : ltac2:(tb__ "0|0|
S3eS4S3cSbS25S1S4fA1S2fS27S2dA6S6A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUEL48 [] NF vcuts48 vexits48 cuts48 exits48 eq_refl eq_refl echeck48). Qed.

Lemma F1_below48 : ltac2:(tb__ "0|0|
S3eS4S58SfS1bS1cS42S20A1A1A1S0SfS48S45A3A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2_below48 : ltac2:(tb__ "0|0|
S3eS4S58SfS1bS1cS42S20A1A1A1S0SfS49S45A3A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Pre48_facts : ltac2:(tb__ "0|0|
S3eS2SfA1S1eS42S20A1A1S24A3"). Proof. reflexivity. Qed.

Section Core.
Variable rho : valuation.
Let a := bv_unsigned (eval rho dst). Let b := bv_unsigned (eval rho src). Let n := bv_unsigned (rw rho 18).

Lemma pre48_disjoint : ltac2:(tb__ "0|0|
S2S40Q40A1A1S56S37S35SbR1S20Vrho;R3R2A6S5bVn;S5cZ2Z3fA2A2S3fS5aS59Va;Vn;A2Vb;A2S3fS5aS59Vb;Vn;A2Va;A2S3eS4fVn;Z0A3A2A2F_;F_;FJ;Fw;Ftp;").
Proof.
  intros tp w J [Hsm _] Hn.
  destruct Hsm as (Hsm & _). destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _).
  cbn [ss_objs ax_S Pre48_0 mkA objs48 app pairwise_disjoint] in Hpd.
  destruct Hpd as (_ & _ & _ & HD & _). apply Forall_inv in HD.
  unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, O_dst', O_src' in HD. cbn [ob_base ob_lo ob_hi fst snd] in HD.
  rewrite !soff_lit_small in HD by lia.
  assert (Es : soff rho vN = n) by (unfold vN; apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Asan_memcpy_proof.soff_var'; subst n; lia). rewrite !Es in HD.
  subst a b. lia.
Qed.

Lemma SPA48_cases : ltac2:(tb__ "0|0|
S37S2S40Q40A1A1S56S35SbR3S20Vrho;R2R1A6S3fS35SbR4S22Vrho;R3R2A6S35SbR4S23Vrho;R3R2A6A2F_;Fw;Ftp;FJ;").
Proof.
  intros J tp w Hw. pose proof (SPA_facts_hold segs J rho Pre48_0 tp w Hw) as HF. rewrite Pre48_facts in HF.
  unfold base48 in HF. apply Forall_app in HF as [HP HF].
  destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Asan_memcpy_proof.pre_Z rho HF) as (Ea & Eb & ZD & ZS & ZN).
  destruct (pre48_disjoint tp w J Hw ltac:(unfold n; lia)) as [H|[H|H]]; [left | right | exfalso; unfold n in H; lia].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Asan_memcpy_proof.facts1 rho HF H) | exact F1_below48].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Asan_memcpy_proof.facts2 rho HF H) | exact F2_below48].
Qed.
End Core.

Section Sum.
Variable ok : world -> Prop.
Variable J : jpredA.
Hypothesis Hok : ok_frameA segs ok J.
Hypothesis Hst : stableA segs NF J.

Lemma cfg48_sound : ltac2:(tb__ "0|0|
S13S2S40Q40A1A1S41S57S41R1S27A3S13S55SbVok;S35SbS3bS13S18S2fR6R1A3Lr;VJ;A2R3R1R4A5S36SbVJ;S2fR5R4S21A6A4FrhoT;F_;FT;Ftp;Frho;").
Proof.
  intros rho tp T HinT rhoT.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  apply (cfg_soundA segs FUEL48 [] NF cuts48 exits48 (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts48) tp HokG HstG check48); [|exact HinT].
  intros E rhoE HinE. destruct HinE as [<-|[]]. apply exit_postA. left; reflexivity.
Qed.

Theorem core48_sum : ltac2:(tb__ "0|0|
S13S2S40Q40A1A1S55SbVok;S35SbVJ;S20R2R1A5S36SbVJ;S2fR2R1S21A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA48_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply triple_disj.
  - eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre48_1 rho tp w Hw) | intros w Hw; exact Hw |].
    apply (cfg48_sound rho tp Pre48_1). left; reflexivity.
  - eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre48_2 rho tp w Hw) | intros w Hw; exact Hw |].
    apply (cfg48_sound rho tp Pre48_2). right; left; reflexivity.
Qed.
End Sum.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.

Lemma cfg48_complete : ltac2:(tb__ "0|0|
S13S2S40Q40A1A1S38S57S38R1S29A3S13S54SbS35SbS3bS13S18S2fR6R1A3Lr;VJ;A2S3dR3A1R1R4A5S36SbVJ;S2fR5R4S21A6A3FrhoT;F_;Fnd;Ftp;Frho;").
Proof.
  intros rho tp nd HinT rhoT.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  apply (cfg_complete_autoIA segs FUEL48 [] NF vcuts48 vexits48 (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts48) tp HstG); [ | exact echeck48 | | exact HinT].
  { intros m Hm. unfold vcuts48 in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[]].
  apply (eexit_post_IA0 segs J NF rho vcuts48 Posts48 (mkVNA P48 0 (SLit 1))). left; reflexivity.
Qed.

Theorem core48_sum_ex : ltac2:(tb__ "0|0|
S13S2S40Q40A1A1S54SbS35SbVJ;S20R2R1A5S36SbVJ;S2fR2R1S21A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA48_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply etriple_disj.
  - eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre48_1 rho tp w Hw) | intros w Hw; exact Hw |].
    apply (cfg48_complete rho tp (mkVNA Pre48_1 1 (SLit 0))). left; reflexivity.
  - eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre48_2 rho tp w Hw) | intros w Hw; exact Hw |].
    apply (cfg48_complete rho tp (mkVNA Pre48_2 1 (SLit 0))). right; left; reflexivity.
Qed.
End SumEx.
End Asan_memcpy48.

(* [comment removed for export] *)
Module Lib_vec_finalize_dup_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sprop"; "sv"; "SLit"; "sprop_eqb"; "SPUle"; "SAlu"; "ss_facts"; "SVar"; "holds"; "ss_objs"; "sv_eqb"; "ss_next"; "cell"; "eval"; "ob_base"; "ob_hi"; "ob_lo"; "sstate"; "DUnknown"; "ob_dflt"; "obj_range"; "odefault"; "rw"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "mul"; "lt"; "sub"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "true"; "nil"; "prod"; "pair"; "app"; "Some"; "fst"; "option"; "false"; "snd"; "None"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "O_got"; "O_rtc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BI"; "batom"; "ASv"; "KU"; "bsumK"; "bsumV"; "bd_nn"; "bd_subst"; "bd_wpos"; "bud_le"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup"; "vSZ"; "vCAP"; "vHD"; "vLS"; "vSRC"; "s_m"; "tv0"; "vU"; "E_m"; "R_m"; "X_fit"; "X_sret2"; "bd_slow"; "nd0"; "objsR"; "P_fail"; "P_ok"; "X_ret1"; "X_ret2"; "X_sret1"; "X_sret1r"; "am_np"; "ndF"; "ndK"; "ndO"; "ndS"; "objsN"; "ohN"; "ohR"; "p_fit"; "vUg"; "O_src"; "Pre_ad"; "Pre_m"; "X_nofit1"; "X_open"; "X_ret"; "X_sret"; "base_fit"; "cutsE"; "exitsE"; "ndKc"; "rcU"; "sel_sret"; "C_K"; "C_open"; "FUEL_ad"; "O_F2"; "O_W"; "T_mnull"; "T_mok0"; "X_K1"; "X_K2"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_nohead"; "X_ret3"; "X_sret3"; "bd_K"; "cutpcs_ad"; "f2_fact"; "fit_facts"; "iH"; "jU"; "ndL"; "ndMok"; "new_facts"; "nofit_fact"; "osR"; "otN"; "p_new"; "pad_fit"; "sel_ret"; "two47"; "used_fit"; "used_new"; "vAR"; "@Stdlib.Lists.List"; "existsb"; "In"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "potK"; "potV"; "JA_pre"; "emeasA"; "JA"; "JLA"; "NDA"; "am_eqb"; "am_subst"; "ejcertA"; "nd_below"; "nodeIA"; "ok_frameKA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_vec_finalize_dup_pf"; "P0_ad"; "ohF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "J_alloc_pre"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_malloc"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect";
"apply_axforms"; "AXSplit"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_vec_finalize_dup_pf.Sum"; "Posts_ad"; "srcz"; "JL"; "f2z"; "srcF"; "srcP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "FFx"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "POT"; "drop_lastA"; "carve_stateA"; "e32"; "open_stateA"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_vec_finalize_dup_pf.AAP"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_vec_finalize_dup_pf.Sum.X"; "openF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T0"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxCellA"; "recellv_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup.
Module AAP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_arena_alloc_pf. End AAP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ADAddr RA.ReallocAddr.
Local Open Scope lazy_bool_scope.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S0S2bSacS3aSa0S7cS8bP64S75S76A7S2dA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C_open_eq : ltac2:(tb__ "0|0|
S0S6Se7S71S50A2S7bA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S0S6SecS6fS56S53S57Sc1SbdS2eSbfA1SbeA3A5S7fA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S0S6SecS6fS56S53S57Sc2SbdS2eSbfA1SbeA3A5S80A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S0S6Se2S70S2cSdS93S13S7S70A1A1A3A2S85A3"). Proof. vm_compute. reflexivity. Qed.
Definition ohF : sobj := Eval vm_compute in last (ss_objs (ax_S X_fit)) O_src.
Lemma objsF_eq : ltac2:(tb__ "0|1|
S0S2aSbA1S16S7S58A1A1M0S31SbS9fSbG0A2S2cSbSb2S2eSbA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_fit3_eq : ltac2:(tb__ "0|0|
S0S6Se2Se5S58S6bS4eA3S31SdS8dS13S7S58A1A1A3A2S83A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret1_eq : ltac2:(tb__ "0|0|
S0S34S6A1Sd3S73S2cSd1Sd2S79A1S2cSd1Sd4Sf1S38S39S79A2U1A2SfZ18A1A2S2eSd1A1A3A3A2S32S6S61A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma rcU_eq : ltac2:(tb__ "0|1|
S0S34S2fS1eS19A2M0A1Sf8S7S61A1S8eS8fS4eA4S32G0S78A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret1r_eq : ltac2:(tb__ "0|0|
S0S6S9S61S33S1eS19S78A3A2S62A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsN_eq : ltac2:(tb__ "0|1|
S0S2aSbA1S16S7S62A1A1S31SbS31SbS68S2cSbS69S2eSbA1M0A3A3S2cSbS95G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret2_eq : ltac2:(tb__ "0|0|
S0S6Se4S62S31SbS68S2cSbS69S2eSbA1A3A3A2S59A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsN2_eq : ltac2:(tb__ "0|0|
S0S2aSbA1S16S7S59A1A1S31SbS68S2cSbS69S2eSbA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret3_eq : ltac2:(tb__ "0|0|
S0S6Se2Se5S59S96S4eA3S31SdS92S13S7S59A1A1A3A2S89A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret1_eq : ltac2:(tb__ "0|0|
S0S34S6A1Sd3S72S2cSd1Sd2S98A1S2eSd1A1A3A2S32S6S5fA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR_eq : ltac2:(tb__ "0|1|
S0S2aSbA1S16S7S5fA1A1S31SbS31SbS5cS2cSbS6aS2eSbA1M0A3A3S2cSbS94G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret2_eq : ltac2:(tb__ "0|0|
S0S6Se4S5fS31SbS5cS2cSbS6aS2eSbA1A3A3A2S60A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR2_eq : ltac2:(tb__ "0|0|
S0S2aSbA1S16S7S60A1A1S31SbS5cS2cSbS6aS2eSbA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret3_eq : ltac2:(tb__ "0|0|
S0S6Se4S60S5cA2S88A3"). Proof. vm_compute. reflexivity. Qed.

Definition P0_ad (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S5S1S24S3dVr;S52A2M0R1A2S28R1S25G0S3dVr;S51A2A2A2A2SdeVCST;Vr;VFB;VFF;R2A5F_;Fa;").

Definition is_src (o : sobj) : bool := ltac2:(tb__ "0|1|
S2bS2bL_;M0S17S1bVo;A1S52A2G0S17S1dVo;A1SfZ0A1A2S17S1cVo;A1S51A2S35X2bx2S35X2bx2").
Definition is_srcX (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S2bS2bL_;S17S33SeSeVr;A3S52A2S17S36SeSeVr;A3S51A2S35X2bx2").

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Variable AInv : ltac2:(tb__ "0|0|
Se9ScS2aS49Q40A1A1Sd6OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sc8S3aVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S5Sf0VCST;R1A2S1S24Z0R2A2S28R2SefA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S5Sf0VXGL;R1A2S1S24Z0R2A2S28R2SefA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2aS2fS2fS5S5A2S5A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
Sa8VAInv;VCST;VXGL;VKc;Sb1VCST;VFB;VFF;A3VFB;VFF;VBX;Sa2Vnd;Aa").
Definition Posts_ad : list (axst * jpostA) := ltac2:(tb__ "0|1|
S2cS2fS6Sb3A2M0S30S6Sb3S5dSdaS64A1A4S2cG0S30S6Sb3S5eSdaS65A1A4S2eG0A1A3A3").

Definition PD_ad : list (axst * ndesc) := ltac2:(tb__ "0|1|
S2cS2fS6Sa1A2M0S30S6Sa1S5dS64A4S2cG0S30S6Sa1S5eS65A4S2eG0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
Sa7VAInv;VCST;VXGL;Sa0VKc;Vrho0;Sb1VCST;VFB;VFF;A3VFB;VFF;VBX;Sa2Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S2fS6Sa1A2Sf4Fn;") := ltac2:(tb__ "0|0|
SaeVAInv;VCST;VXGL;Sa0VKc;Vrho0;Sb1VCST;VFB;VFF;A3VFB;VFF;VBX;Sa2Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sb4S3aSa0Vrho0;Vtp0;Sd8A5").

Definition srcF (F : list sprop) : Prop := ltac2:(tb__ "0|1|
S1S0S2bS9dSdS10S11SfZ1A1S4eA2A1VF;A3S2dA3S1S0S2bS9dSdS10S11S4eS51A2A1VF;A3S2dA3S1S0S2bS9dSdS10S11S51SfS26Z2Z20A2A1A2A1VF;A3S2dA3S1S0S2bS9dSdS10S11SfZ1000A1S52A2A1VF;A3S2dA3S1S0S2bS9dSdS10S11S12Sb0S52S51A3S14P1eA1M0A2A1VF;A3S2dA3S1S0S2bS9dSdS10S11S52G0A2A1VF;A3S2dA3S0S2bS9dSdS10S11G0SfZ7fffff800000A1A2A1VF;A3S2dA3A2A2A2A2A2A2").
Record srcz (rho : valuation) : Prop := SZ_ {
  sz_n : 1 <= uval rho vSZ <= uval rho vLS; sz_L : uval rho vLS <= 2 ^ 32;
  sz_src : 4096 <= uval rho vSRC /\ uval rho vSRC + uval rho vLS <= bv_unsigned (rw rho V_TOP);
  sz_top : bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma srcz_of : ltac2:(tb__ "0|0|
ScS2aSdA1ScaSdS15R2A1R1A3SdcR2A1Sd9R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & BT).
  pose proof (holds_mem _ _ _ HF BT) as HT2. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  rewrite !uval_lit in H1, H3, H4, HT2 by lia.
  rewrite uval_add_small in H5 by (pose proof (uval_range rho vSRC); pose proof (uval_range rho vLS); lia).
  constructor; lia.
Qed.
Ltac basez_tac HF := exact (AAP.basez_of _ _ HF ltac:(repeat split; vm_compute; reflexivity)).
Ltac srcz_tac HF := exact (srcz_of _ _ HF ltac:(repeat split; vm_compute; reflexivity)).

Definition f2z (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S24S25S3dVrho;S14PaA1A2Z20A2S26Z2Z2fA2A2").
Lemma f2z_of : ltac2:(tb__ "0|0|
ScS2aSdA1ScaSdS15R2A1R1A3S0S2bS9dSdS10S8cA1R2A3S2dA3S0S2bS9dSdS10S11S14PaA1SfS99A1A2A1R3A3S2dA3SdbR5A1F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF B1 B2. pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. zf H1. zf H2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold two47, RA.two47 in *. rewrite uval_lit in H1, H2 by lia.
  unfold f2z. unfold sp_entry in H1. rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia. exact H1.
Qed.
Ltac f2z_tac HF := exact (f2z_of _ _ HF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).

Definition srcP (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S5S1S24S3dVrho;S52A2M0R1A2S28R1S25G0S3dVrho;S51A2A2A2A2SdeVCST;Vrho0;VFB;VFF;R2A5F_;Fa;").
Lemma srcP_of : ltac2:(tb__ "0|0|
ScSb1VCST;VFB;VFF;Vrho0;A4SeaSa0Vrho0;R2A3SddR3A1F_;F_;Frho;").
Proof.
  intros rho HP [Hav _] a Ha. apply HP. unfold uval in *. cbn [eval vSRC vLS] in *.
  rewrite (Hav 13%positive) by reflexivity. rewrite (Hav 16%positive) by reflexivity. exact Ha.
Qed.
Lemma src_range : ltac2:(tb__ "0|2|
ScS5Sd9R2A1S1S24S33S5S5S21R3S6dA2M0A3R2A2S28R2S36S5S5G0A3A2A2S1S24S3dR4S52A2M1R3A2S28R3S25G1S3dR4S51A2A2A2A2F_;F_;Fa;Frho;").
Proof.
  intros rho a SZ Hr. destruct SZ as [S1 S2 S3 S4]. unfold obj_range, obj_lo_of, obj_hi_of, O_src in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite (soff_smallu rho vLS) in Hr by lia. unfold uval in *. lia.
Qed.
Lemma pclMA_x : ltac2:(tb__ "0|0|
ScS5SdeVCST;Vrho0;VFB;VFF;R1A5SdeVCST;Vrho0;Sf5VFB;R3S54A3SdfVFF;R3S2eS2fS2fSeS5A2SeA2A1A3R2A5F_;Fa;Frho;").
Proof.
  intros rho a [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | exact Hr].
  - right; right; right. exists f, s, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin | exact Hr].
Qed.

Lemma objs_ok_ad : ltac2:(tb__ "0|6|
ScS2aSbA1Sf2R2A1Sd9R3A1SddR4A1SdbR5A1SbS9eSbR1R6A3S2S1S0SeS1bR2A1M0S14PaA1A3S1S0SeS1dR2A1M1SfN40A1A3S1S0SeS1cR2A1M2SfZ0A1M3A3S0S22S20R2A1S1fA3M4A2A2A2S2S0SbR2S7eA3S2S1S0SeG0S9cA3S1S0SeG1G3A3S1S0SeG2SfZ40A1A3G4A2A2A2S2S2S0SbR2S3bA3S0SbR2S3cA3A2S2S0SbR2S6dA3S3S2aS19A1M5G5S0SbR3S7dR1A1A3Lcells;A2A2A2A2A2A2F_;Fo;S0S5Sf6Vrho0;A1S4aQ40S23R7Sc5A2A2A3Se8VCST;Vrho0;VFB;VFF;R8S54S2eS2fS2fSeS5A2SeA2A1R7A8F_;F_;F_;F_;F_;F_;Fobjs;Frho;").
Proof.
  intros rho objs BZ SZ SP F2 Hcls ET o a Ho Hr.
  destruct (Hcls o Ho) as [C|[C|[C|[C|[->|(cells & ->)]]]]].
  6: { left. left. unfold O_F2 in Hr. apply range_lit' in Hr; [|lia|lia]. destruct BZ as [[B1 B2] _ _ _ _]. unfold f2z in F2. rewrite ET. lia. }
  1-4: refine (AAP.objs_ok_gen CST FB FF rho0 rho [o] BZ _ ET o a (or_introl eq_refl) Hr); intros o' [<-|[]]; auto 10.
  left. apply pclMA_x. apply SP. exact (src_range rho a SZ Hr).
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S5S2aS49Q40A1A1Sb8F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4cS6ScS2aS49Q40A1A1Sb8ScaSdS15R3A1S13S7R4A1A1A3VTR;S4bS3aR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sb8Sb8Sb8Sb9R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
Sb8Sb8Sb9S4R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S4cS4cS6S6SceS2aSbA1M0S2aS2fS6Sb3A2M1A1S2aS2fSeSeA2M2A1Sb8ScS2aS49Q40A1A1M3G2S9eG2R1R5A3S9eG2R2S8RbA1A3F_;Fr;S0S34G0A1Sb7RaR9R8A3S32G0R7A2A3S0S2bSb6RbRaR9R8ScbG1S6S33S6Sb3A2R7A4A5S2dA3ScG3VTR;S4bS3aRfRdR2R1A5Sb4S3aS18S7RdA1A1R2R1RaA5A2Ftp1;Frho1;S2aSd7A1M4Sd5Sd6S4dS3aR9R8R10S30G4Se0R3Se1R2R1A2A4A5R13RaR9R4R2A4R13ScdSccRbRfSbcR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S6Sb3G4Sd5Sd6ScG3G4Sd5Sd6S9eG1S30S6Sb3RaR9A4R14A3S4dS3aR12R11R19S30G4Se0R9Se1R8R7A2A4A5R1cR13R12RaR8A4SeaS18S7R1aA1A1ScdSccR14R18SbcR9R13RaA3A3R19A2R8A3S4dS3aR9R8ReS30G4Se0R7Se1R6R5A2A4A5ReScdSccR16R1aSbcRbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sf9R17SbcRcR16RdA3R1bR1cR1dR10R1eR19RbA9ScSebR18SbcRdR17ReA3R1cR1dS7R1eA1S7R1fA1S7R11A1R1RcA9VTR;S4bS3aSb5R11ScdSccR19R1dSbcReR18RfA3A3R1eA2R18RdRcA5SfaR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S4bS3aR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Se9ScS2aS49Q40A1A1VTR;S4bS3aSc0VAInv;S2eSbfA1M0SbeR3VKc;S14PcA1A6Sc4SbdG0SbeA3R2R1A5Sb4S3aSa0R2R1Sc3SbdVAInv;VCST;VXGL;G0SbeR3VKc;A8A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S6Sa1S2fS5SeA2M0ScS2aS49Q40A1A1M1S5G1S9eS2fS2fS6Sa1A2M2G0A2S30G2G0S30S6Sa1R7R6A4R5A4S75A3S1S24Z0Sa6S30G2G0S30S6Sa1R8R7A4R6A4R5A2M3A2S28G3R3A2A2VTR;S4bS3aVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S6Sa1ScS2aS49Q40A1A1M0S5G0S9eS2fS6Sb3A2S30S6Sb3R6SdaR5A1A4Sd8A3VTR;S4bS3aVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd];
  match goal with |- context [bv_unsigned (eval ?r ?e)] => pose proof (U_range (eval r e)) end; unfold M64v in *; lia.
Tactic Notation "innth" integer(k) := do k right; left; reflexivity.

Lemma X_P_fail : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0VTR;S4bS3aVJAv;S64A1S5dR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. left. reflexivity. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0VTR;S4bS3aVJAv;S65A1S5eR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. right. left. reflexivity. Qed.

Lemma X_X_open : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0S24S27Z5bS26Z2Z40A2A2R2A2VTR;S4bS3aVJAv;S5bA1S71R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndO) C_open rho' tp w)).
  { intros w Hw.
    destruct (JA_open segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] CH vHD true X_open rho tp w) as (rho' & _ & Hw');
      [vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | exact Hw |].
    - intros Ai rho1 tp1 md1 HF HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. split.
      + apply objs_ok_ad; [basez_tac HF | srcz_tac HF | exact (srcP_of rho HP0 Hav) | f2z_tac HF | | exact ET].
        intros o Ho. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; first [solve [auto 12] | (do 5 right; eexists; reflexivity)].
      + intros r a Hr Ha. assert (HX : In r [(vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
        pose proof (srcz_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [S1 S2] ST].
        destruct HX as [<-|[<-|[]]]; cbn [fst snd] in Ha; [rewrite uval_lit in Ha by lia; unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *; lia | lia].
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER C_open ndO (90, z0)); [innth 1 | meas].
Qed.

Lemma X_X_nohead : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0S24S27Z51S26Z2Z40A2A2R2A2VTR;S4bS3aVJAv;S5bA1S87R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_slow ndS (80, z0) (rho_sub rho s_nohead)); [innth 2 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv0 [] (CH ++ [BIc 1 0 AV0; BIc 0 1 AK0]) (AHead vHD false)) ndS);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  apply (JA_pot_out0 segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HBX); [vm_compute; reflexivity | exact Hw].
Qed.

Lemma and16_eq : and_hmask 18446744073709551600 = Some 16. Proof. vm_compute. reflexivity. Qed.
Lemma fit_arith : ltac2:(tb__ "0|c|
ScS24S3dR1S50A2Z7fffff800000A2S24S3dR2S55A2S3dR2S4fA2A2S24S3dR3S4fA2S29S26Z2M0Z28A2Z21A2A2S24S3dR4S4eA2S26G0Z20M1A2A2S1S0S5S3dR5S74A2M2S25S25S3dR5S50A2M3G1A2M4S3dR5S55A2M5A2A3S1S1S24G2S3dR5S6bA2M6A2S24G6S25G2ZfM7A2M8A2A2S1S0S5S3dR5S97A2M9S29G6G2A2A3S1S0S5S3dR5S9aA2S25S25G5S3dR5S4eA2MaA2G9A2A3S1S0S5S3dR5S12Sb0S74SfG7A1MbA3A2G8A3S1S0S5S3dR5S12Sb0S6bS4eA3A2S25G6GaA2A3S1S0S5S3dR5S12Sb0S50Se6S4fA1A3A2S25G3S25S3dR5S4fA2G1A2A2A3S1S0S5S3dR5S12Sb0S55S12Sb0S4eGbA3A3A2S25G5S25GaG7A2A2A3S0S5S3dR5S12Sb0S50SfG1A1A3A2G4A3A2A2A2A2A2A2A2A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho Hh Hu Hc Hn.
  pose proof (uval_range rho vHD) as R1. pose proof (uval_range rho vU) as R2. pose proof (uval_range rho vCAP) as R3. pose proof (uval_range rho vSZ) as R4.
  assert (EB : uval rho base_fit = uval rho vHD + 32 + uval rho vU).
  { unfold base_fit. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (E15 : uval rho (SAlu ALU_ADD base_fit (SLit 15)) = uval rho base_fit + 15).
  { rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (EP : uval rho base_fit <= uval rho p_fit <= uval rho base_fit + 15).
  { assert (Ep : p_fit = SAlu ALU_AND (SAlu ALU_ADD base_fit (SLit 15)) (SLit 18446744073709551600)) by reflexivity. rewrite Ep.
    unfold uval at 2 3. rewrite (U_and_hmask rho _ _ 16 and16_eq). change (bv_unsigned (eval rho (SAlu ALU_ADD base_fit (SLit 15)))) with (uval rho (SAlu ALU_ADD base_fit (SLit 15))).
    rewrite E15. pose proof (Z.mod_pos_bound (uval rho base_fit + 15) 16 ltac:(lia)). lia. }
  assert (EPAD : uval rho pad_fit = uval rho p_fit - uval rho base_fit).
  { unfold pad_fit. unfold uval at 1. rewrite U_sub. change (bv_unsigned (eval rho p_fit)) with (uval rho p_fit). change (bv_unsigned (eval rho base_fit)) with (uval rho base_fit).
    unfold M64v. apply Z.mod_small. lia. }
  assert (E1 : uval rho (SAlu ALU_ADD pad_fit vSZ) = uval rho pad_fit + uval rho vSZ) by (rewrite uval_add_small by (rewrite EPAD; lia); lia).
  split; [exact EB|]. split; [exact EP|]. split; [exact EPAD|]. split; [|split; [exact E15|split; [|split; [|split]]]].
  - unfold used_fit. rewrite uval_add_small by (rewrite E1, EPAD; lia). rewrite E1. lia.
  - rewrite uval_add_small by lia. reflexivity.
  - unfold e32. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
  - rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
  - rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
Qed.

Definition openF (F : list sprop) : Prop := ltac2:(tb__ "0|1|
S1S0S2bS9dSdS10S11S50S14P1eA1M0A2A1VF;A3S2dA3S1S0S2bS9dSdS10S11S55S4fA2A1VF;A3S2dA3S1S0S2bS9dSdS10S11S4fSfS29S26Z2Z28A2Z21A2A1A2A1VF;A3S2dA3S1S0S2bS9dSdS10S11SfZ10000A1S4fA2A1VF;A3S2dA3S1S0S2bS9dSdS10S11S12Sb0S50Se6S4fA1A3G0A2A1VF;A3S2dA3S1S0S2bS9dSdS10S11SfZ1000A1S50A2A1VF;A3S2dA3S0S2bS9dSdS10S11G0SfZ7fffff800000A1A2A1VF;A3S2dA3A2A2A2A2A2A2").
Lemma openz : ltac2:(tb__ "0|6|
ScS2aSdA1ScaSdS15R2A1R1A3Sf3R2A1S24S3dR4S4eA2S26Z2M0Z20M1A2A2S1S24S3dR5S50A2M2Z7fffff800000M3A2S1S24S3dR5S55A2S3dR5S4fA2M4A2S1S24G4S29S26G0Z28A2Z21A2A2S1S24Z10000G4A2S1S24S25G2S25G4G1A2A2S3dR5S14P1eA1A2M5A2S1S24Z1000G2A2S24G5G3A2A2A2A2A2A2A2F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & BT) Hn.
  pose proof (holds_mem _ _ _ HF BT) as HT2. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  rewrite !uval_lit in H3, H4, H6, HT2 by lia.
  destruct (fit_arith rho ltac:(lia) H2 H3 Hn) as (_ & _ & _ & _ & _ & _ & E7 & _). rewrite E7 in H5. lia.
Qed.
Ltac openz_tac HF SZ := exact (openz _ _ HF ltac:(repeat split; vm_compute; reflexivity) ltac:(destruct SZ; lia)).

Lemma X_X_nofitO : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0VTR;S4bS3aVJAv;S66A1S86R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF. apply TR_false. intros w _.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & _).
  factz HF (SPBranch BC_LTU (SAlu ALU_XOR vSZ (SLit 18446744073709551615)) pad_fit) H0.
  assert (EX : uval rho (SAlu ALU_XOR vSZ (SLit 18446744073709551615)) = 2 ^ 64 - 1 - uval rho vSZ).
  { unfold uval. rewrite (U_xor_m1 rho vSZ 18446744073709551615 ltac:(reflexivity)). reflexivity. }
  rewrite EX in H0. destruct SZ. lia.
Qed.

Lemma X_X_nofit : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0S24S27Z51S26Z2Z40A2A2R2A2VTR;S4bS3aVJAv;S66A1S84R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & EN & _).
  factz HF (SPNot (SPBranch BC_GEU vCAP used_fit)) H0. rewrite EN in H0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndS) C_slow rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (JA_close_np segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_open vHD vNX vCAP vU X_nofit
                  (removelast (ss_objs (ax_S X_nofit))) (AA.O_hdr vHD vNX vCAP vU) rho tp tr ms md) as CL.
    specialize (CL ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; left; reflexivity) eq_refl Hw).
    set (rho1 := rho_absorb rho [AA.O_hdr vHD vNX vCAP vU] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv0 [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. change (drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit)))) with X_nofit1 in CL.
      apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | vm_compute; reflexivity |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65537 mod M64v) with 65537.
      assert (EU : forall e, eval rho1 e = eval rho e) by (intros e; unfold rho1; apply eval_absorb).
      rewrite EU. change (bv_unsigned (eval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16))))) with (uval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16)))).
      destruct SZ as [S1 S2 S3 S4]. pose proof (uval_range rho vU).
      rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
      rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
    exists (rho_sub rho1 s_nofit).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv0 [] bd_open am_np) ndS);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact CL2]. }
  apply TR_exw. intros rho'. apply (REENTER C_slow ndS (80, z0)); [innth 2 | meas].
Qed.

Lemma X_X_fit : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0S24S27Z33S26Z2Z40A2A2R2A2VTR;S4bS3aVJAv;S66A1S58R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & EN & E15 & E72 & EHC & EU15 & EH32).
  factz HF (SPBranch BC_GEU vCAP used_fit) H0. rewrite EN in H0.
  eapply TR_pre; [|apply (REENTER C_loop ndL (50, SAlu ALU_SUB vSZ vI) (rho_sub rho s_fit)); [innth 6 | meas]].
  intros w Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_fit3 C_loop s_fit (NDA tv0 [] bd_open (AOpen vHD vNX vCAP [(p_fit, vSZ)])) ndL);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  rewrite <- X_fit3_eq. apply (SPA_refacts_JA segs _ rho (carve_stateA X_fit p_fit vSZ) (fit_facts ++ ss_facts (ax_S X_fit))); [| vm_compute; reflexivity |].
  - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_open vHD vNX vCAP p_fit vSZ X_fit rho tp w);
      [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact Hw].
    + intros r HFr. assert (SZr : srcz r) by srcz_tac HFr.
      assert (OZr : uval r vHD <= 140737479966720 /\ uval r vU <= uval r vCAP /\ uval r vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval r vCAP
                    /\ uval r vHD + (uval r vCAP + 32) <= uval r (SVar 30) /\ 4096 <= uval r vHD /\ uval r (SVar 30) <= 140737479966720) by openz_tac HFr SZr.
      destruct OZr as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
      destruct (fit_arith r Y1 Y2 Y3 ltac:(destruct SZr; lia)) as (EB' & EP' & EPAD' & EN' & _).
      factz HFr (SPBranch BC_GEU vCAP used_fit) H1. rewrite EN' in H1. pose proof (uval_range r vU). destruct SZr. lia.
    + intros Ai rho1 tp1 md1 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. split.
      * intros o a Ho Hr. rewrite objsF_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
        -- destruct (objs_ok_ad rho (removelast (ss_objs (ax_S X_fit))) ltac:(basez_tac HF) SZ (srcP_of rho HP0 Hav) ltac:(f2z_tac HF)
                      ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; first [solve [auto 12] | (do 5 right; eexists; reflexivity)])
                      ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
        -- right; right. unfold ohF in Hr. apply range_lit' in Hr; [|lia|lia]. unfold vHD, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vHD. lia.
      * intros r a Hr Ha.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
        assert (HX : In r [(vHD, e32 vCAP); (vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
        -- unfold e32 in Ha. rewrite uval_add_small in Ha by (rewrite uval_lit by lia; lia). rewrite uval_lit in Ha by lia.
           pose proof (uval_range rho vHD). lia.
        -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *. lia.
        -- destruct SZ as [_ _ [S1 S2] ST]. lia.
  - intros tr md _ HF2. apply Forall_app. split; [|exact HF2].
    unfold fit_facts. pose proof (uval_range rho vU). pose proof (uval_range rho vHD). destruct SZ.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
      rewrite ?E15, ?E72, ?EHC, ?EU15, ?EH32, ?EN; rewrite ?uval_lit by lia; lia.
Qed.

Lemma sums_slow : ltac2:(tb__ "0|2|
ScS1S0S5S44S5aR1A2S25Sa4S3dR1S6cA2M0A1S25S27Z2S3dR1S4eA2M1A2Z60A2A2A3S0S5S43S5aR1A2S25Sa3G0A1S25S27Z4G1A2Z40A2A2A3A2Fr;").
Proof.
  intros r. unfold bd_slow. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vUg) as (-> & -> & _).
  unfold CH. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. lia.
Qed.
Lemma sums_K : ltac2:(tb__ "0|7|
ScSeS1S0S5S44S31S3eS2cS3eS3fZ1M0Z0M1S2cS2fS5S40A2M2S30S5S40G0S41R1A1A4S2eG2A1M3A3G1A4S2cS3eS3fG1G0G3S27Z2S42A2M4A4S2eS3eA1A3A3Se3S4eA1A3M5R2A2S25S3dR2R1A2Sa4S3dR2S4eA2M6A1A2A3S1S0S5S43G5R2A2S25G4Sa3G6A1A2A3S1S45G5R2A2S0S2bS47G5A1S2dA3A2A2A2Fk;Fr;").
Proof.
  intros r k. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vSZ) as (-> & -> & NN & WP).
  cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. pose proof (uval_range r k). unfold KU.
  split; [lia|]. split; [lia|]. split; [|reflexivity].
  apply bd_nn_app. split; [|exact NN]. repeat constructor; unfold bival; cbn [lfval aval bi_f bi_c]; lia.
Qed.

Lemma pay_K_arith : ltac2:(tb__ "0|5|
S5S5S5S24Z0R3A2S1S24Z1R3A2S24R3S26Z2M0Z20M1A2A2A2S24Z10001S25S25R5R4A2Z10M2A2A2S2S1S0S5R4Z10000M3A3S28S25R5G2A2M4G3A2A2S1S0S5R4G4A3S24G3G4A2A2A2S1S24S25S25R5G1A2Sa4R6A1A2S25Sa4R7A1S25S27G0R6A2Z60A2A2A2S24S25S27G0S42A2Sa3R6A1A2S25Sa3R7A1S25S27Z4R6A2Z40A2A2A2A2F_;F_;F_;F_;Fk;Fn;Fug;").
Proof. intros ug n k Hu Hn Hs Hk. unfold potV, potK, AV0, AK0, KU. destruct Hk as [[-> Hc]|[-> Hc]]; split; lia. Qed.

Lemma pay_K : ltac2:(tb__ "0|b|
S6SeSdcS13S7R2A1A1A1S0S2bS9dSdS10S11SfZ10001A1S12Sb0S6cS12Sb0S4eSfZ10M0A1A3A3A2A1S13S7R3A1A1A3S2dA3S0S2bS9dSdS10S11S6cSfS26Z2M1Z28A2A1A2A1S13S7R4A1A1A3S2dA3ScScaSdS15R1A1S13S7R6A1A1M2A3Sd9R2A1S2S1S0S5S3dR3R7A2M3Z10020A3S28S25S3dR3S4eA2M4G0A2M5Z10000M6A2A2S1S0S5G3S25G4Z30A2A3S24G6G5A2A2A2F_;F_;Fr;SedSa0Vrho0;Sb1VCST;VFB;VFF;A3G2SfZ0M7A1G7S5aS31S3eS2cS3eS3fZ1M8G7S2cS2fS5S40A2M9S30S5S40G8S41R5A1A4S2eG9A1MaA3G7A4S2cS3eS3fG7G8GaS27G1S42A2A4S2eS3eA1A3A3Se3S4eA1A3A8F_;F_;F_;F_;Fk;FX;").
Proof.
  intros X k HB Hug1 Hug2 HK. destruct (sums_K rho0 k) as (_ & _ & _ & WP). split; [exact WP|]. split; [lia|]. intros r HF _ _ _. unfold pay_sem.
  assert (SZ : srcz r) by exact (srcz_of _ _ HF HB).
  destruct (sums_K r k) as (-> & -> & NN & _). destruct (sums_slow r) as [-> ->]. rewrite uval_lit by lia.
  pose proof (holds_mem _ _ _ HF Hug1) as H1. pose proof (holds_mem _ _ _ HF Hug2) as H2. zf H1. zf H2.
  repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H2.
  rewrite !uval_lit in H1, H2 by lia. pose proof (uval_range r vUg). destruct SZ as [S1 S2 S3 S4].
  rewrite uval_add_small in H1 by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia.
  pose proof (HK r HF ltac:(split; assumption)) as HKr.
  destruct (pay_K_arith (uval r vUg) (uval r vSZ) (uval r k - 32) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [A B].
  split; [lia|]. split; [lia | exact NN].
Qed.

Lemma X_X_K : ltac2:(tb__ "0|8|
S6SceSeScS2aS49Q40A1A1M0S5G0SedSa0Vrho0;Sb1VCST;VFB;VFF;A3S13S7R7A1A1SfZ0M1A1G1S5aS31S3eS2cS3eS3fZ1M2G1S2cS2fS5S40A2M3S30S5S40G2S41R5A1A4S2eG3A1M4A3G1A4S2cS3eS3fG1G2G4S27Z2M5S42A2A4S2eS3eA1A3M6A3Se3S4eA1M7A3A8S0S2bSaR8S7aR7A3S2dA3S0S2bSd0R8Sa0A2S2dA3S0S2bSfbSa0S18S7RaA1A1A2S2dA3S0S2bSadS18S7RbA1A1Sa9S54S2eS2fS2fSeS5A2SeA2A1S31S3eS2cS3eS3fG2G1S2cG3S30S5S40G2S41R9A1A4G4A3G1A4G6A3G7A3S63A4A2S2dA3S0S2bS48S13S7RcA1A1S46RbS8aA2S31S3eS2cS3eS3fG2G1S2cG3S30S5S40G2S41RaA1A4G4A3G1A4G6A3G7A3A3S2dA3S0S2bSaaSabRcS63A2S63A2S2dA3S0S2bSf7RdS54S54A3S2dA3S24S27Z4cS26G5Z40A2A2RaA2VTR;S4bS3aVJAv;S67A1R10RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fk;Fs;FX;").
Proof.
  intros X s k rho tp b tp0 HPAY He Hid Hnf Hnb Hle Ham Htv Hb.
  eapply TR_pre; [|apply (REENTER C_K ndKc (75, z0) (rho_sub rho s)); [innth 3 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X C_K s (NDA tv0 [] ([BI 1 0 [(1, ASv k)] 0; BI 0 1 [] (2 * KU)] ++ POT vSZ) am_np) ndKc);
    [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | exact Ham |].
  apply (JA_repay segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue tv0 [] bd_slow _ am_np X rho tp w HPAY Hw).
Qed.
Lemma X_X_K1 : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0S24S27Z4cS26Z2Z40A2A2R2A2VTR;S4bS3aVJAv;S67A1S81R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K1 s_K1 (SLit 65568));
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [repeat split; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros r HF SZ. left. factz HF (SPBranch BC_LTU (SAlu ALU_ADD vSZ (SLit 16)) (SLit 65536)) H1.
  destruct SZ. rewrite !uval_lit in * by lia. rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia. lia.
Qed.
Lemma X_X_K2 : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0S24S27Z4cS26Z2Z40A2A2R2A2VTR;S4bS3aVJAv;S67A1S82R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K2 s_K2 (SAlu ALU_ADD vSZ (SLit 48)));
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [repeat split; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros r HF SZ. right. factz HF (SPNot (SPBranch BC_LTU (SAlu ALU_ADD vSZ (SLit 16)) (SLit 65536))) H1.
  destruct SZ. rewrite !uval_lit in * by lia. rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia.
  rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma site_m : ltac2:(tb__ "0|1|
ScSeeVAInv;VCST;VXGL;Sa0Vrho0;Sb1VCST;VFB;VFF;A3VFB;VFF;S56S53S57R1S77S37S5A1Se9Sd5S1S1S24Z1S3dR3ScfS53PcA2A2M0A2S28G0S26Z2Z27A2A2A2Sc9S2eSbfA1SbeScdSccR3S57R1A3S53A2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndKc] in HN, HD, HZ, HFR.
  assert (SZ : srcz rho) by srcz_tac HF. pose proof (srcP_of rho HP0 Hav) as SP.
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None is_src R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
    + intros o a Ho Hb Hr. unfold is_src in Hb.
      apply lazy_andb_prop in Hb as [H1 Hb]. apply lazy_andb_prop in Hb as [H2 H3].
      apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
      apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HT). apply SP. apply (src_range rho a SZ).
      destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi] in H1, H2, H3. subst.
      unfold obj_range, obj_lo_of, obj_hi_of, O_src in Hr |- *. cbn [ob_base ob_lo ob_hi fst snd] in Hr |- *. exact Hr.
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) is_srcX (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
    + intros r a Hr Hb Ha. unfold is_srcX in Hb. apply lazy_andb_prop in Hb as [H1 H2]. apply sv_eqb_sound in H1. apply sv_eqb_sound in H2.
      left. apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HT). apply SP. destruct r as [rb rl]. cbn [fst snd] in H1, H2, Ha. subst. exact Ha.
    + exact I.
  - change (wsub_get s_m 12) with (e32 vK). factz HF (SPUle (SLit 65536) vK) H1. factz HF (SPUle vK (SLit (2 ^ 32 + 16))) H2.
    rewrite !uval_lit in H1, H2 by lia. unfold e32. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma X_E_m : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0S24S27Z42S26Z2Z40A2A2R2A2VTR;S4bS3aVJAv;S77A1S56R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (malloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp ndKc bd_m (FAM b tp0) CMALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull ndM (65, z0)); [innth 4 | meas].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok ndMok (65, z0)); [innth 5 | meas]].
    intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). vm_compute. reflexivity.
Qed.

Lemma used_new_val : ltac2:(tb__ "0|0|
ScS0S49Q40A1S1aR1S4eA2S1aR1S9bA2A3Fr;").
Proof.
  intros r. reflexivity.
Qed.

Lemma X_X_sret : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0S24S27Z33S26Z2Z40A2A2R2A2VTR;S4bS3aVJAv;S91A1S73R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndL) C_loop rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_sret X_sret1 tp _ X_sret1_eq Hw) as H1.
    pose proof (AxCellA.SPA_recellv segs _ rho X_sret1 iH jU vSZ (fst rcU) (snd rcU) tp _ ltac:(rewrite rcU_eq; destruct rcU; reflexivity)
                  ltac:(vm_compute; reflexivity) (fun _ => used_new_val rho) H1) as H1r.
    rewrite X_sret1r_eq in H1r.
    pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m bd_m2 0 blkN vHD vK vSZ
                  X_sret1r objsN ohN otN rho tp tr ms md objsN_eq eq_refl) as H2.
    specialize (H2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) H1r).
    rewrite X_sret2_eq in H2. cbn [remove_nth fst blkN] in H2.
    set (rho1 := rho_absorb rho [otN] (vms md tp ms)) in H2.
    assert (HF1 : Forall (holds rho1) (ss_facts (ax_S X_sret2))) by exact (smatchA_facts segs _ _ _ _ (proj1 H2)).
    assert (SZ1 : srcz rho1) by srcz_tac HF1.
    factz HF1 (SPUle (SAlu ALU_ADD (SVar pN) (e32 vK)) (SVar 30)) HE1. factz HF1 (SPUle (SVar pN) (SVar 30)) HE2.
    factz HF1 (SPUle (SLit 65536) vK) HK1. factz HF1 (SPUle vK (SLit (2 ^ 32 + 16))) HK2. factz HF1 (SPUle (SAlu ALU_ADD vSZ (SLit 16)) vK) HK3.
    factz HF1 (SPUle (SVar 30) (SLit 140737479966720)) HT30. rewrite !uval_lit in HT30, HK1, HK2 by lia.
    pose proof (uval_range rho1 (SVar pN)) as RP. pose proof (uval_range rho1 vK) as RK.
    assert (EK : uval rho1 (e32 vK) = uval rho1 vK + 32) by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small in HE1 by (rewrite EK; lia). rewrite EK in HE1.
    rewrite uval_add_small in HK3 by (rewrite uval_lit by lia; destruct SZ1; lia). rewrite uval_lit in HK3 by lia.
    assert (EPn : uval rho1 p_new = uval rho1 (SVar pN) + 32) by (unfold p_new; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    assert (H3 : SPA segs (JAv (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD vK [(p_new, vSZ)]))) X_sret3 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_sret3_eq.
      apply (SPA_refacts_JA segs _ rho1 (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2))); [| vm_compute; reflexivity |].
      - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_m2 (SVar pN) vHD vK p_new vSZ X_sret2 rho1 tp _);
          [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact H2].
        + intros r HFr. assert (SZr : srcz r) by srcz_tac HFr.
          factz HFr (SPUle (SAlu ALU_ADD vSZ (SLit 16)) vK) HK3'. factz HFr (SPUle vK (SLit (2 ^ 32 + 16))) HK2'. rewrite uval_lit in HK2' by lia.
          rewrite uval_add_small in HK3' by (rewrite uval_lit by lia; destruct SZr; lia). rewrite uval_lit in HK3' by lia.
          pose proof (uval_range r (SVar pN)). unfold p_new.
          rewrite uval_add_small by (rewrite uval_lit by lia; factz HFr (SPUle (SVar pN) (SVar 30)) HE; factz HFr (SPUle (SVar 30) (SLit 140737479966720)) HT30'; rewrite uval_lit in HT30' by lia; lia).
          rewrite uval_lit by lia. destruct SZr. lia.
        + intros Ai rho2 tp2 md2 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho1 Hav eq_refl) as ET. split.
          * intros o a Ho Hr. rewrite objsN2_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
            -- destruct (objs_ok_ad rho1 objsN ltac:(basez_tac HF') SZ1 (srcP_of rho1 HP0 Hav) ltac:(f2z_tac HF')
                          ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; first [solve [auto 12] | (do 5 right; eexists; reflexivity)])
                          ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
            -- right; right. unfold ohN in Hr. apply range_lit' in Hr; [|lia|lia]. unfold pN. lia.
          * intros r a Hr Ha.
            assert (HX : In r [(vAR, SLit 64); (vSRC, vLS); (SVar pN, e32 vK)]) by exact Hr. clear Hr.
            pose proof (AAP.basez_of rho1 _ HF' ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
            destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
            -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *. lia.
            -- destruct SZ1 as [_ _ [S1 S2] ST]. lia.
            -- rewrite EK in Ha. lia.
      - intros tr' md' _ HF2. apply Forall_app. split; [|exact HF2].
        unfold new_facts. destruct SZ1. change (bv_unsigned (rw rho1 V_TOP)) with (uval rho1 (SVar 30)) in *.
        assert (EPS : uval rho1 (SAlu ALU_ADD p_new vSZ) = uval rho1 p_new + uval rho1 vSZ) by (rewrite uval_add_small by lia; lia).
        assert (EHC : uval rho1 (SAlu ALU_ADD (SVar pN) (e32 vK)) = uval rho1 (SVar pN) + (uval rho1 vK + 32)) by (rewrite uval_add_small by (rewrite EK; lia); rewrite EK; lia).
        repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
          rewrite ?EPS, ?EHC, ?EPn; rewrite ?uval_lit by lia; lia. }
    exists (rho_sub rho1 s_sret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_sret3 C_loop s_sret (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD vK [(p_new, vSZ)])) ndL);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
  apply TR_exw. intros rho'. apply (REENTER C_loop ndL (50, SAlu ALU_SUB vSZ vI)); [innth 6 | meas].
Qed.

Lemma X_X_ret : ltac2:(tb__ "0|1|
ScS2aS49Q40A1A1M0S5G0VTR;S4bS3aVJAv;S90A1S72R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndK) P_ok rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_ret X_ret1 tp _ X_ret1_eq Hw) as H1.
    pose proof (JA_unslot segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HNP tv0 [] bd_loop vH vNXl vCAPl vP vSZ
                  X_ret1 (objsR ++ [ohR]) osR rho tp tr ms md objsR_eq ltac:(vm_compute; reflexivity) H1) as H2.
    rewrite X_ret2_eq in H2. set (rho1 := rho_absorb rho [osR] (vms md tp ms)) in H2.
    pose proof (JA_close segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_loop [] vH vNXl vCAPl vUc
                  X_ret2 objsR ohR rho1 tp tr ms md objsR2_eq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; left; reflexivity) eq_refl ltac:(vm_compute; reflexivity) H2) as H3.
    rewrite X_ret3_eq in H3. set (rho2 := rho_absorb rho1 [ohR] (vms md tp ms)) in H3.
    exists (rho_sub rho2 s_ret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_ret3 P_ok s_ret (NDA tv0 [] [] (AHead vH true)) ndK);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
  apply TR_exw. intros rho'. apply X_P_ok.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S6Sa1S2fS5SeA2M0ScS2aS49Q40A1A1M1G1S9eS2fS2fS6Sa1A2M2G0A2S30G2G0S30S6Sa1R6R5A4R4A4S76A3VTR;S4bS3aVJAv;R6A1R7R4R3A5VFAM;Sa6S30G2G0S30S6Sa1R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_open. meas.
  - apply X_X_nohead. meas.
  - apply X_X_nofitO.
  - apply X_X_fit. meas.
  - apply X_X_nofit. meas.
  - apply X_X_K1. meas.
  - apply X_X_K2. meas.
  - apply X_E_m. meas.
  - apply X_X_sret. meas.
  - apply X_X_ret.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
SafS3aVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sc6S3aSbdVAInv;VCST;VXGL;A5").

Theorem arena_dup_sum : ltac2:(tb__ "0|0|
S2aS49Q40A1A1SbbS3aVok;S4bS3aSa5VAInv;VCST;VXGL;VKc;Sb1VCST;VFB;VFF;A3VFB;VFF;VBX;Sa2S5bAaS6eVrho0;R1A5Sb4S3aSa0Vrho0;R1Sd8A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc ALA FUEL_ad cutpcs_ad 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertA_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_false segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok))
         with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_ad CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_ad P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sc7S3aSbdVAInv;VCST;VXGL;A5").

Theorem arena_dup_sum_ex : ltac2:(tb__ "0|0|
S2aS49Q40A1A1SbaS3aS4bS3aSa5VAInv;VCST;VXGL;VKc;Sb1VCST;VFB;VFF;A3VFB;VFF;VBX;Sa2S5bAaS6eVrho0;R1A5Sb4S3aSa0Vrho0;R1Sd8A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc ALA FUEL_ad cutpcs_ad 100 cutsE exitsE (Q tp0) ejcertA_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_false segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_ad CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_ad P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_finalize_dup_pf.

(* [comment removed for export] *)
Module Lib_finalize_shape_dup1_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sprop"; "sv"; "SLit"; "SPUle"; "sprop_eqb"; "SAlu"; "ss_facts"; "SVar"; "ss_objs"; "sv_eqb"; "holds"; "ss_next"; "cell"; "eval"; "ob_base"; "ob_hi"; "ob_lo"; "sstate"; "DUnknown"; "ob_dflt"; "obj_range"; "odefault"; "rw"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "mul"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "O_got"; "O_rtc"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "true"; "nil"; "prod"; "pair"; "app"; "Some"; "fst"; "option"; "false"; "snd"; "None"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BI"; "batom"; "ASv"; "KU"; "bsumK"; "bsumV"; "bd_nn"; "bd_subst"; "bd_wpos"; "bud_le"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Lib_finalize_shape_dup1"; "vSZ"; "vCAP"; "vHD"; "vLS"; "vSRC"; "s_m"; "tv0"; "vU"; "E_m"; "R_m"; "X_fit"; "X_sret2"; "bd_slow"; "nd0"; "objsR"; "P_fail"; "P_ok"; "X_ret1"; "X_ret2"; "X_sret1"; "X_sret1r"; "am_np"; "ndF"; "ndK"; "ndO"; "ndS"; "objsN"; "ohN"; "ohR"; "p_fit"; "vUg"; "O_src"; "Pre_ad"; "Pre_m"; "X_nofit1"; "X_open"; "X_ret"; "X_sret"; "base_fit"; "cutsE"; "exitsE"; "ndKc"; "rcU"; "sel_sret"; "C_K"; "C_open"; "FUEL_ad"; "O_W"; "T_mnull"; "T_mok0"; "X_K1"; "X_K2"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_nohead"; "X_ret3"; "X_sret3"; "bd_K"; "cutpcs_ad"; "fit_facts"; "iH"; "jU"; "ndL"; "ndMok"; "new_facts"; "nofit_fact"; "osR"; "otN"; "p_new"; "pad_fit"; "sel_ret"; "used_fit"; "used_new"; "vAR"; "@Stdlib.Lists.List"; "existsb"; "In"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "potK"; "potV"; "JA_pre"; "emeasA"; "JA"; "JLA"; "NDA"; "am_eqb"; "am_subst"; "ejcertA"; "nd_below"; "nodeIA"; "ok_frameKA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_shape_dup1_pf"; "P0_ad"; "ohF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "J_alloc_pre"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_malloc"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXSplit"; "@Corelib.Lists.ListDef"; "Forall"; "map";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_shape_dup1_pf.Sum"; "Posts_ad"; "srcz"; "JL"; "srcF"; "srcP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "FFx"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "POT"; "drop_lastA"; "carve_stateA"; "e32"; "open_stateA"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_shape_dup1_pf.AAP"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_shape_dup1_pf.Sum.X"; "openF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T0"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxCellA"; "recellv_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Lib_finalize_shape_dup1.
Module AAP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_arena_alloc_pf. End AAP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ADAddr RA.ReallocAddr.
Local Open Scope lazy_bool_scope.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S0S2dSa8S29S9cS7bS89P64S74S75A7S2fA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C_open_eq : ltac2:(tb__ "0|0|
S0S5Se2S70S4fA2S7aA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S0S5Se7S6eS55S52S56SbdSb9S30SbbA1SbaA3A5S7dA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S0S5Se7S6eS55S52S56SbeSb9S30SbbA1SbaA3A5S7eA3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S0S5SddS6fS2eScS90S12S6S6fA1A1A3A2S83A3"). Proof. vm_compute. reflexivity. Qed.
Definition ohF : sobj := Eval vm_compute in last (ss_objs (ax_S X_fit)) O_src.
Lemma objsF_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S57A1A1M0S33SaS9bSaG0A2S2eSaSaeS30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_fit3_eq : ltac2:(tb__ "0|0|
S0S5SddSe0S57S6aS4dA3S33ScS8aS12S6S57A1A1A3A2S81A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret1_eq : ltac2:(tb__ "0|0|
S0S36S5A1ScdS72S2eScbSccS78A1S2eScbSceSecS3aS3bS78A2U1A2SeZ18A1A2S30ScbA1A3A3A2S34S5S60A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma rcU_eq : ltac2:(tb__ "0|1|
S0S36S31S1dS18A2M0A1Sf3S6S60A1S8bS8cS4dA4S34G0S77A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret1r_eq : ltac2:(tb__ "0|0|
S0S5S8S60S35S1dS18S77A3A2S61A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsN_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S61A1A1S33SaS33SaS67S2eSaS68S30SaA1M0A3A3S2eSaS92G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret2_eq : ltac2:(tb__ "0|0|
S0S5SdfS61S33SaS67S2eSaS68S30SaA1A3A3A2S58A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsN2_eq : ltac2:(tb__ "0|0|
S0S2cSaA1S14S6S58A1A1S33SaS67S2eSaS68S30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret3_eq : ltac2:(tb__ "0|0|
S0S5SddSe0S58S93S4dA3S33ScS8fS12S6S58A1A1A3A2S87A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret1_eq : ltac2:(tb__ "0|0|
S0S36S5A1ScdS71S2eScbSccS95A1S30ScbA1A3A2S34S5S5eA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S5eA1A1S33SaS33SaS5bS2eSaS69S30SaA1M0A3A3S2eSaS91G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret2_eq : ltac2:(tb__ "0|0|
S0S5SdfS5eS33SaS5bS2eSaS69S30SaA1A3A3A2S5fA3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR2_eq : ltac2:(tb__ "0|0|
S0S2cSaA1S14S6S5fA1A1S33SaS5bS2eSaS69S30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret3_eq : ltac2:(tb__ "0|0|
S0S5SdfS5fS5bA2S86A3"). Proof. vm_compute. reflexivity. Qed.

Definition P0_ad (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S4S1S23S3cVr;S51A2M0R1A2S27R1S24G0S3cVr;S50A2A2A2A2Sd9VCST;Vr;VFB;VFF;R2A5F_;Fa;").

Definition is_src (o : sobj) : bool := ltac2:(tb__ "0|1|
S2dS2dL_;M0S15S1aVo;A1S51A2G0S15S1cVo;A1SeZ0A1A2S15S1bVo;A1S50A2S37X2dx2S37X2dx2").
Definition is_srcX (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S2dS2dL_;S15S35SdSdVr;A3S51A2S15S38SdSdVr;A3S50A2S37X2dx2").

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Variable AInv : ltac2:(tb__ "0|0|
Se4SbS2cS48Q40A1A1Sd2OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sc4S29VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S4SebVCST;R1A2S1S23Z0R2A2S27R2SeaA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S4SebVXGL;R1A2S1S23Z0R2A2S27R2SeaA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2cS31S31S4S4A2S4A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
Sa4VAInv;VCST;VXGL;VKc;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eVnd;Aa").
Definition Posts_ad : list (axst * jpostA) := ltac2:(tb__ "0|1|
S2eS31S5SafA2M0S32S5SafS5cSd6S63A1A4S2eG0S32S5SafS5dSd6S64A1A4S30G0A1A3A3").

Definition PD_ad : list (axst * ndesc) := ltac2:(tb__ "0|1|
S2eS31S5S9dA2M0S32S5S9dS5cS63A4S2eG0S32S5S9dS5dS64A4S30G0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
Sa3VAInv;VCST;VXGL;S9cVKc;Vrho0;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S31S5S9dA2SefFn;") := ltac2:(tb__ "0|0|
SaaVAInv;VCST;VXGL;S9cVKc;Vrho0;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sb0S29S9cVrho0;Vtp0;Sd4A5").

Definition srcF (F : list sprop) : Prop := ltac2:(tb__ "0|1|
S1S0S2dS99ScS10SfSeZ1A1S4dA2A1VF;A3S2fA3S1S0S2dS99ScS10SfS4dS50A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS50SeS25Z2Z20A2A1A2A1VF;A3S2fA3S1S0S2dS99ScS10SfSeZ1000A1S51A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS11SacS51S50A3S13P1eA1M0A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS51G0A2A1VF;A3S2fA3S0S2dS99ScS10SfG0SeZ7fffff800000A1A2A1VF;A3S2fA3A2A2A2A2A2A2").
Record srcz (rho : valuation) : Prop := SZ_ {
  sz_n : 1 <= uval rho vSZ <= uval rho vLS; sz_L : uval rho vLS <= 2 ^ 32;
  sz_src : 4096 <= uval rho vSRC /\ uval rho vSRC + uval rho vLS <= bv_unsigned (rw rho V_TOP);
  sz_top : bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma srcz_of : ltac2:(tb__ "0|0|
SbS2cScA1ScfScS16R2A1R1A3Sd7R2A1Sd5R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & BT).
  pose proof (holds_mem _ _ _ HF BT) as HT2. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  rewrite !uval_lit in H1, H3, H4, HT2 by lia.
  rewrite uval_add_small in H5 by (pose proof (uval_range rho vSRC); pose proof (uval_range rho vLS); lia).
  constructor; lia.
Qed.
Ltac basez_tac HF := exact (AAP.basez_of _ _ HF ltac:(repeat split; vm_compute; reflexivity)).
Ltac srcz_tac HF := exact (srcz_of _ _ HF ltac:(repeat split; vm_compute; reflexivity)).

Definition srcP (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S4S1S23S3cVrho;S51A2M0R1A2S27R1S24G0S3cVrho;S50A2A2A2A2Sd9VCST;Vrho0;VFB;VFF;R2A5F_;Fa;").
Lemma srcP_of : ltac2:(tb__ "0|0|
SbSadVCST;VFB;VFF;Vrho0;A4Se5S9cVrho0;R2A3Sd8R3A1F_;F_;Frho;").
Proof.
  intros rho HP [Hav _] a Ha. apply HP. unfold uval in *. cbn [eval vSRC vLS] in *.
  rewrite (Hav 13%positive) by reflexivity. rewrite (Hav 16%positive) by reflexivity. exact Ha.
Qed.
Lemma src_range : ltac2:(tb__ "0|2|
SbS4Sd5R2A1S1S23S35S4S4S20R3S6cA2M0A3R2A2S27R2S38S4S4G0A3A2A2S1S23S3cR4S51A2M1R3A2S27R3S24G1S3cR4S50A2A2A2A2F_;F_;Fa;Frho;").
Proof.
  intros rho a SZ Hr. destruct SZ as [S1 S2 S3 S4]. unfold obj_range, obj_lo_of, obj_hi_of, O_src in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite (soff_smallu rho vLS) in Hr by lia. unfold uval in *. lia.
Qed.
Lemma pclMA_x : ltac2:(tb__ "0|0|
SbS4Sd9VCST;Vrho0;VFB;VFF;R1A5Sd9VCST;Vrho0;Sf0VFB;R3S53A3SdaVFF;R3S30S31S31SdS4A2SdA2A1A3R2A5F_;Fa;Frho;").
Proof.
  intros rho a [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | exact Hr].
  - right; right; right. exists f, s, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin | exact Hr].
Qed.

Lemma objs_ok_ad : ltac2:(tb__ "0|5|
SbS2cSaA1SedR2A1Sd5R3A1Sd8R4A1SaS9aSaR1R5A3S2S1S0SdS1aR2A1M0S13PaA1A3S1S0SdS1cR2A1M1SeN40A1A3S1S0SdS1bR2A1M2SeZ0A1M3A3S0S21S1fR2A1S1eA3M4A2A2A2S2S0SaR2S7cA3S2S1S0SdG0S98A3S1S0SdG1G3A3S1S0SdG2SeZ40A1A3G4A2A2A2S2S2S0SaR2S2aA3S0SaR2S2bA3A2S0SaR2S6cA3A2A2A2A2F_;Fo;S0S4Sf1Vrho0;A1S49Q40S22R6Sc1A2A2A3Se3VCST;Vrho0;VFB;VFF;R7S53S30S31S31SdS4A2SdA2A1R6A8F_;F_;F_;F_;F_;Fobjs;Frho;").
Proof.
  intros rho objs BZ SZ SP Hcls ET o a Ho Hr.
  destruct (Hcls o Ho) as [C|[C|[C|[C| ->]]]].
  1-4: refine (AAP.objs_ok_gen CST FB FF rho0 rho [o] BZ _ ET o a (or_introl eq_refl) Hr); intros o' [<-|[]]; auto 10.
  left. apply pclMA_x. apply SP. exact (src_range rho a SZ Hr).
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S4S2cS48Q40A1A1Sb4F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4bS5SbS2cS48Q40A1A1Sb4ScfScS16R3A1S12S6R4A1A1A3VTR;S4aS29R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sb4Sb4Sb4Sb5R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
Sb4Sb4Sb5S3R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S4bS4bS5S5Sc8S2cSaA1M0S2cS31S5SafA2M1A1S2cS31SdSdA2M2A1Sb4SbS2cS48Q40A1A1M3G2S9aG2R1R5A3S9aG2R2S7RbA1A3F_;Fr;S0S36G0A1Sb3RaR9R8A3S34G0R7A2A3S0S2dSb2RbRaR9R8Sd0G1S5S35S5SafA2R7A4A5S2fA3SbG3VTR;S4aS29RfRdR2R1A5Sb0S29S17S6RdA1A1R2R1RaA5A2Ftp1;Frho1;S2cSd3A1M4Sd1Sd2S4cS29R9R8R10S32G4SdbR3SdcR2R1A2A4A5R13RaR9R4R2A4R13Sc7Sc6RbRfSb8R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S5SafG4Sd1Sd2SbG3G4Sd1Sd2S9aG1S32S5SafRaR9A4R14A3S4cS29R12R11R19S32G4SdbR9SdcR8R7A2A4A5R1cR13R12RaR8A4Se5S17S6R1aA1A1Sc7Sc6R14R18Sb8R9R13RaA3A3R19A2R8A3S4cS29R9R8ReS32G4SdbR7SdcR6R5A2A4A5ReSc7Sc6R16R1aSb8RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sf4R17Sb8RcR16RdA3R1bR1cR1dR10R1eR19RbA9SbSe6R18Sb8RdR17ReA3R1cR1dS6R1eA1S6R1fA1S6R11A1R1RcA9VTR;S4aS29Sb1R11Sc7Sc6R19R1dSb8ReR18RfA3A3R1eA2R18RdRcA5Sf5R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S4aS29R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Se4SbS2cS48Q40A1A1VTR;S4aS29SbcVAInv;S30SbbA1M0SbaR3VKc;S13PcA1A6Sc0Sb9G0SbaA3R2R1A5Sb0S29S9cR2R1SbfSb9VAInv;VCST;VXGL;G0SbaR3VKc;A8A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S5S9dS31S4SdA2M0SbS2cS48Q40A1A1M1S4G1S9aS31S31S5S9dA2M2G0A2S32G2G0S32S5S9dR7R6A4R5A4S74A3S1S23Z0Sa2S32G2G0S32S5S9dR8R7A4R6A4R5A2M3A2S27G3R3A2A2VTR;S4aS29VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S5S9dSbS2cS48Q40A1A1M0S4G0S9aS31S5SafA2S32S5SafR6Sd6R5A1A4Sd4A3VTR;S4aS29VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd];
  match goal with |- context [bv_unsigned (eval ?r ?e)] => pose proof (U_range (eval r e)) end; unfold M64v in *; lia.
Tactic Notation "innth" integer(k) := do k right; left; reflexivity.

Lemma X_P_fail : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S63A1S5cR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. left. reflexivity. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S64A1S5dR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. right. left. reflexivity. Qed.

Lemma X_X_open : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z5bS25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S5aA1S70R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndO) C_open rho' tp w)).
  { intros w Hw.
    destruct (JA_open segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] CH vHD true X_open rho tp w) as (rho' & _ & Hw');
      [vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | exact Hw |].
    - intros Ai rho1 tp1 md1 HF HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. split.
      + apply objs_ok_ad; [basez_tac HF | srcz_tac HF | exact (srcP_of rho HP0 Hav) | | exact ET].
        intros o Ho. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 10.
      + intros r a Hr Ha. assert (HX : In r [(vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
        pose proof (srcz_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [S1 S2] ST].
        destruct HX as [<-|[<-|[]]]; cbn [fst snd] in Ha; [rewrite uval_lit in Ha by lia; unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *; lia | lia].
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER C_open ndO (90, z0)); [innth 1 | meas].
Qed.

Lemma X_X_nohead : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z51S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S5aA1S85R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_slow ndS (80, z0) (rho_sub rho s_nohead)); [innth 2 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv0 [] (CH ++ [BIc 1 0 AV0; BIc 0 1 AK0]) (AHead vHD false)) ndS);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  apply (JA_pot_out0 segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HBX); [vm_compute; reflexivity | exact Hw].
Qed.

Lemma and16_eq : and_hmask 18446744073709551600 = Some 16. Proof. vm_compute. reflexivity. Qed.
Lemma fit_arith : ltac2:(tb__ "0|c|
SbS23S3cR1S4fA2Z7fffff800000A2S23S3cR2S54A2S3cR2S4eA2A2S23S3cR3S4eA2S28S25Z2M0Z28A2Z21A2A2S23S3cR4S4dA2S25G0Z20M1A2A2S1S0S4S3cR5S73A2M2S24S24S3cR5S4fA2M3G1A2M4S3cR5S54A2M5A2A3S1S1S23G2S3cR5S6aA2M6A2S23G6S24G2ZfM7A2M8A2A2S1S0S4S3cR5S94A2M9S28G6G2A2A3S1S0S4S3cR5S96A2S24S24G5S3cR5S4dA2MaA2G9A2A3S1S0S4S3cR5S11SacS73SeG7A1MbA3A2G8A3S1S0S4S3cR5S11SacS6aS4dA3A2S24G6GaA2A3S1S0S4S3cR5S11SacS4fSe1S4eA1A3A2S24G3S24S3cR5S4eA2G1A2A2A3S1S0S4S3cR5S11SacS54S11SacS4dGbA3A3A2S24G5S24GaG7A2A2A3S0S4S3cR5S11SacS4fSeG1A1A3A2G4A3A2A2A2A2A2A2A2A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho Hh Hu Hc Hn.
  pose proof (uval_range rho vHD) as R1. pose proof (uval_range rho vU) as R2. pose proof (uval_range rho vCAP) as R3. pose proof (uval_range rho vSZ) as R4.
  assert (EB : uval rho base_fit = uval rho vHD + 32 + uval rho vU).
  { unfold base_fit. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (E15 : uval rho (SAlu ALU_ADD base_fit (SLit 15)) = uval rho base_fit + 15).
  { rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (EP : uval rho base_fit <= uval rho p_fit <= uval rho base_fit + 15).
  { assert (Ep : p_fit = SAlu ALU_AND (SAlu ALU_ADD base_fit (SLit 15)) (SLit 18446744073709551600)) by reflexivity. rewrite Ep.
    unfold uval at 2 3. rewrite (U_and_hmask rho _ _ 16 and16_eq). change (bv_unsigned (eval rho (SAlu ALU_ADD base_fit (SLit 15)))) with (uval rho (SAlu ALU_ADD base_fit (SLit 15))).
    rewrite E15. pose proof (Z.mod_pos_bound (uval rho base_fit + 15) 16 ltac:(lia)). lia. }
  assert (EPAD : uval rho pad_fit = uval rho p_fit - uval rho base_fit).
  { unfold pad_fit. unfold uval at 1. rewrite U_sub. change (bv_unsigned (eval rho p_fit)) with (uval rho p_fit). change (bv_unsigned (eval rho base_fit)) with (uval rho base_fit).
    unfold M64v. apply Z.mod_small. lia. }
  assert (E1 : uval rho (SAlu ALU_ADD pad_fit vSZ) = uval rho pad_fit + uval rho vSZ) by (rewrite uval_add_small by (rewrite EPAD; lia); lia).
  split; [exact EB|]. split; [exact EP|]. split; [exact EPAD|]. split; [|split; [exact E15|split; [|split; [|split]]]].
  - unfold used_fit. rewrite uval_add_small by (rewrite E1, EPAD; lia). rewrite E1. lia.
  - rewrite uval_add_small by lia. reflexivity.
  - unfold e32. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
  - rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
  - rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
Qed.

Definition openF (F : list sprop) : Prop := ltac2:(tb__ "0|1|
S1S0S2dS99ScS10SfS4fS13P1eA1M0A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS54S4eA2A1VF;A3S2fA3S1S0S2dS99ScS10SfS4eSeS28S25Z2Z28A2Z21A2A1A2A1VF;A3S2fA3S1S0S2dS99ScS10SfSeZ10000A1S4eA2A1VF;A3S2fA3S1S0S2dS99ScS10SfS11SacS4fSe1S4eA1A3G0A2A1VF;A3S2fA3S1S0S2dS99ScS10SfSeZ1000A1S4fA2A1VF;A3S2fA3S0S2dS99ScS10SfG0SeZ7fffff800000A1A2A1VF;A3S2fA3A2A2A2A2A2A2").
Lemma openz : ltac2:(tb__ "0|6|
SbS2cScA1ScfScS16R2A1R1A3SeeR2A1S23S3cR4S4dA2S25Z2M0Z20M1A2A2S1S23S3cR5S4fA2M2Z7fffff800000M3A2S1S23S3cR5S54A2S3cR5S4eA2M4A2S1S23G4S28S25G0Z28A2Z21A2A2S1S23Z10000G4A2S1S23S24G2S24G4G1A2A2S3cR5S13P1eA1A2M5A2S1S23Z1000G2A2S23G5G3A2A2A2A2A2A2A2F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & BT) Hn.
  pose proof (holds_mem _ _ _ HF BT) as HT2. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  rewrite !uval_lit in H3, H4, H6, HT2 by lia.
  destruct (fit_arith rho ltac:(lia) H2 H3 Hn) as (_ & _ & _ & _ & _ & _ & E7 & _). rewrite E7 in H5. lia.
Qed.
Ltac openz_tac HF SZ := exact (openz _ _ HF ltac:(repeat split; vm_compute; reflexivity) ltac:(destruct SZ; lia)).

Lemma X_X_nofitO : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S65A1S84R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF. apply TR_false. intros w _.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & _).
  factz HF (SPBranch BC_LTU (SAlu ALU_XOR vSZ (SLit 18446744073709551615)) pad_fit) H0.
  assert (EX : uval rho (SAlu ALU_XOR vSZ (SLit 18446744073709551615)) = 2 ^ 64 - 1 - uval rho vSZ).
  { unfold uval. rewrite (U_xor_m1 rho vSZ 18446744073709551615 ltac:(reflexivity)). reflexivity. }
  rewrite EX in H0. destruct SZ. lia.
Qed.

Lemma X_X_nofit : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z51S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S65A1S82R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & EN & _).
  factz HF (SPNot (SPBranch BC_GEU vCAP used_fit)) H0. rewrite EN in H0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndS) C_slow rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (JA_close_np segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_open vHD vNX vCAP vU X_nofit
                  (removelast (ss_objs (ax_S X_nofit))) (AA.O_hdr vHD vNX vCAP vU) rho tp tr ms md) as CL.
    specialize (CL ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; left; reflexivity) eq_refl Hw).
    set (rho1 := rho_absorb rho [AA.O_hdr vHD vNX vCAP vU] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv0 [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. change (drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit)))) with X_nofit1 in CL.
      apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | vm_compute; reflexivity |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65537 mod M64v) with 65537.
      assert (EU : forall e, eval rho1 e = eval rho e) by (intros e; unfold rho1; apply eval_absorb).
      rewrite EU. change (bv_unsigned (eval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16))))) with (uval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16)))).
      destruct SZ as [S1 S2 S3 S4]. pose proof (uval_range rho vU).
      rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
      rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
    exists (rho_sub rho1 s_nofit).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv0 [] bd_open am_np) ndS);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact CL2]. }
  apply TR_exw. intros rho'. apply (REENTER C_slow ndS (80, z0)); [innth 2 | meas].
Qed.

Lemma X_X_fit : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z33S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S65A1S57R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & EN & E15 & E72 & EHC & EU15 & EH32).
  factz HF (SPBranch BC_GEU vCAP used_fit) H0. rewrite EN in H0.
  eapply TR_pre; [|apply (REENTER C_loop ndL (50, SAlu ALU_SUB vSZ vI) (rho_sub rho s_fit)); [innth 6 | meas]].
  intros w Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_fit3 C_loop s_fit (NDA tv0 [] bd_open (AOpen vHD vNX vCAP [(p_fit, vSZ)])) ndL);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  rewrite <- X_fit3_eq. apply (SPA_refacts_JA segs _ rho (carve_stateA X_fit p_fit vSZ) (fit_facts ++ ss_facts (ax_S X_fit))); [| vm_compute; reflexivity |].
  - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_open vHD vNX vCAP p_fit vSZ X_fit rho tp w);
      [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact Hw].
    + intros r HFr. assert (SZr : srcz r) by srcz_tac HFr.
      assert (OZr : uval r vHD <= 140737479966720 /\ uval r vU <= uval r vCAP /\ uval r vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval r vCAP
                    /\ uval r vHD + (uval r vCAP + 32) <= uval r (SVar 30) /\ 4096 <= uval r vHD /\ uval r (SVar 30) <= 140737479966720) by openz_tac HFr SZr.
      destruct OZr as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
      destruct (fit_arith r Y1 Y2 Y3 ltac:(destruct SZr; lia)) as (EB' & EP' & EPAD' & EN' & _).
      factz HFr (SPBranch BC_GEU vCAP used_fit) H1. rewrite EN' in H1. pose proof (uval_range r vU). destruct SZr. lia.
    + intros Ai rho1 tp1 md1 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. split.
      * intros o a Ho Hr. rewrite objsF_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
        -- destruct (objs_ok_ad rho (removelast (ss_objs (ax_S X_fit))) ltac:(basez_tac HF) SZ (srcP_of rho HP0 Hav)
                      ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 12)
                      ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
        -- right; right. unfold ohF in Hr. apply range_lit' in Hr; [|lia|lia]. unfold vHD, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vHD. lia.
      * intros r a Hr Ha.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
        assert (HX : In r [(vHD, e32 vCAP); (vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
        -- unfold e32 in Ha. rewrite uval_add_small in Ha by (rewrite uval_lit by lia; lia). rewrite uval_lit in Ha by lia.
           pose proof (uval_range rho vHD). lia.
        -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *. lia.
        -- destruct SZ as [_ _ [S1 S2] ST]. lia.
  - intros tr md _ HF2. apply Forall_app. split; [|exact HF2].
    unfold fit_facts. pose proof (uval_range rho vU). pose proof (uval_range rho vHD). destruct SZ.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
      rewrite ?E15, ?E72, ?EHC, ?EU15, ?EH32, ?EN; rewrite ?uval_lit by lia; lia.
Qed.

Lemma sums_slow : ltac2:(tb__ "0|2|
SbS1S0S4S43S59R1A2S24Sa0S3cR1S6bA2M0A1S24S26Z2S3cR1S4dA2M1A2Z60A2A2A3S0S4S42S59R1A2S24S9fG0A1S24S26Z4G1A2Z40A2A2A3A2Fr;").
Proof.
  intros r. unfold bd_slow. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vUg) as (-> & -> & _).
  unfold CH. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. lia.
Qed.
Lemma sums_K : ltac2:(tb__ "0|7|
SbSdS1S0S4S43S33S3dS2eS3dS3eZ1M0Z0M1S2eS31S4S3fA2M2S32S4S3fG0S40R1A1A4S30G2A1M3A3G1A4S2eS3dS3eG1G0G3S26Z2S41A2M4A4S30S3dA1A3A3SdeS4dA1A3M5R2A2S24S3cR2R1A2Sa0S3cR2S4dA2M6A1A2A3S1S0S4S42G5R2A2S24G4S9fG6A1A2A3S1S44G5R2A2S0S2dS46G5A1S2fA3A2A2A2Fk;Fr;").
Proof.
  intros r k. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vSZ) as (-> & -> & NN & WP).
  cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. pose proof (uval_range r k). unfold KU.
  split; [lia|]. split; [lia|]. split; [|reflexivity].
  apply bd_nn_app. split; [|exact NN]. repeat constructor; unfold bival; cbn [lfval aval bi_f bi_c]; lia.
Qed.

Lemma pay_K_arith : ltac2:(tb__ "0|5|
S4S4S4S23Z0R3A2S1S23Z1R3A2S23R3S25Z2M0Z20M1A2A2A2S23Z10001S24S24R5R4A2Z10M2A2A2S2S1S0S4R4Z10000M3A3S27S24R5G2A2M4G3A2A2S1S0S4R4G4A3S23G3G4A2A2A2S1S23S24S24R5G1A2Sa0R6A1A2S24Sa0R7A1S24S26G0R6A2Z60A2A2A2S23S24S26G0S41A2S9fR6A1A2S24S9fR7A1S24S26Z4R6A2Z40A2A2A2A2F_;F_;F_;F_;Fk;Fn;Fug;").
Proof. intros ug n k Hu Hn Hs Hk. unfold potV, potK, AV0, AK0, KU. destruct Hk as [[-> Hc]|[-> Hc]]; split; lia. Qed.

Lemma pay_K : ltac2:(tb__ "0|b|
S5SdSd7S12S6R2A1A1A1S0S2dS99ScS10SfSeZ10001A1S11SacS6bS11SacS4dSeZ10M0A1A3A3A2A1S12S6R3A1A1A3S2fA3S0S2dS99ScS10SfS6bSeS25Z2M1Z28A2A1A2A1S12S6R4A1A1A3S2fA3SbScfScS16R1A1S12S6R6A1A1M2A3Sd5R2A1S2S1S0S4S3cR3R7A2M3Z10020A3S27S24S3cR3S4dA2M4G0A2M5Z10000M6A2A2S1S0S4G3S24G4Z30A2A3S23G6G5A2A2A2F_;F_;Fr;Se8S9cVrho0;SadVCST;VFB;VFF;A3G2SeZ0M7A1G7S59S33S3dS2eS3dS3eZ1M8G7S2eS31S4S3fA2M9S32S4S3fG8S40R5A1A4S30G9A1MaA3G7A4S2eS3dS3eG7G8GaS26G1S41A2A4S30S3dA1A3A3SdeS4dA1A3A8F_;F_;F_;F_;Fk;FX;").
Proof.
  intros X k HB Hug1 Hug2 HK. destruct (sums_K rho0 k) as (_ & _ & _ & WP). split; [exact WP|]. split; [lia|]. intros r HF _ _ _. unfold pay_sem.
  assert (SZ : srcz r) by exact (srcz_of _ _ HF HB).
  destruct (sums_K r k) as (-> & -> & NN & _). destruct (sums_slow r) as [-> ->]. rewrite uval_lit by lia.
  pose proof (holds_mem _ _ _ HF Hug1) as H1. pose proof (holds_mem _ _ _ HF Hug2) as H2. zf H1. zf H2.
  repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H2.
  rewrite !uval_lit in H1, H2 by lia. pose proof (uval_range r vUg). destruct SZ as [S1 S2 S3 S4].
  rewrite uval_add_small in H1 by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia.
  pose proof (HK r HF ltac:(split; assumption)) as HKr.
  destruct (pay_K_arith (uval r vUg) (uval r vSZ) (uval r k - 32) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [A B].
  split; [lia|]. split; [lia | exact NN].
Qed.

Lemma X_X_K : ltac2:(tb__ "0|8|
S5Sc8SdSbS2cS48Q40A1A1M0S4G0Se8S9cVrho0;SadVCST;VFB;VFF;A3S12S6R7A1A1SeZ0M1A1G1S59S33S3dS2eS3dS3eZ1M2G1S2eS31S4S3fA2M3S32S4S3fG2S40R5A1A4S30G3A1M4A3G1A4S2eS3dS3eG1G2G4S26Z2M5S41A2A4S30S3dA1A3M6A3SdeS4dA1M7A3A8S0S2dS9R8S79R7A3S2fA3S0S2dScaR8S9cA2S2fA3S0S2dSf6S9cS17S6RaA1A1A2S2fA3S0S2dSa9S17S6RbA1A1Sa5S53S30S31S31SdS4A2SdA2A1S33S3dS2eS3dS3eG2G1S2eG3S32S4S3fG2S40R9A1A4G4A3G1A4G6A3G7A3S62A4A2S2fA3S0S2dS47S12S6RcA1A1S45RbS88A2S33S3dS2eS3dS3eG2G1S2eG3S32S4S3fG2S40RaA1A4G4A3G1A4G6A3G7A3A3S2fA3S0S2dSa6Sa7RcS62A2S62A2S2fA3S0S2dSf2RdS53S53A3S2fA3S23S26Z4cS25G5Z40A2A2RaA2VTR;S4aS29VJAv;S66A1R10RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fk;Fs;FX;").
Proof.
  intros X s k rho tp b tp0 HPAY He Hid Hnf Hnb Hle Ham Htv Hb.
  eapply TR_pre; [|apply (REENTER C_K ndKc (75, z0) (rho_sub rho s)); [innth 3 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X C_K s (NDA tv0 [] ([BI 1 0 [(1, ASv k)] 0; BI 0 1 [] (2 * KU)] ++ POT vSZ) am_np) ndKc);
    [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | exact Ham |].
  apply (JA_repay segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue tv0 [] bd_slow _ am_np X rho tp w HPAY Hw).
Qed.
Lemma X_X_K1 : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z4cS25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S66A1S7fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K1 s_K1 (SLit 65568));
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [repeat split; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros r HF SZ. left. factz HF (SPBranch BC_LTU (SAlu ALU_ADD vSZ (SLit 16)) (SLit 65536)) H1.
  destruct SZ. rewrite !uval_lit in * by lia. rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia. lia.
Qed.
Lemma X_X_K2 : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z4cS25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S66A1S80R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K2 s_K2 (SAlu ALU_ADD vSZ (SLit 48)));
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [repeat split; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros r HF SZ. right. factz HF (SPNot (SPBranch BC_LTU (SAlu ALU_ADD vSZ (SLit 16)) (SLit 65536))) H1.
  destruct SZ. rewrite !uval_lit in * by lia. rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia.
  rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma site_m : ltac2:(tb__ "0|1|
SbSe9VAInv;VCST;VXGL;S9cVrho0;SadVCST;VFB;VFF;A3VFB;VFF;S55S52S56R1S76S39S4A1Se4Sd1S1S1S23Z1S3cR3Sc9S52PcA2A2M0A2S27G0S25Z2Z27A2A2A2Sc5S30SbbA1SbaSc7Sc6R3S56R1A3S52A2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndKc] in HN, HD, HZ, HFR.
  assert (SZ : srcz rho) by srcz_tac HF. pose proof (srcP_of rho HP0 Hav) as SP.
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None is_src R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
    + intros o a Ho Hb Hr. unfold is_src in Hb.
      apply lazy_andb_prop in Hb as [H1 Hb]. apply lazy_andb_prop in Hb as [H2 H3].
      apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
      apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HT). apply SP. apply (src_range rho a SZ).
      destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi] in H1, H2, H3. subst.
      unfold obj_range, obj_lo_of, obj_hi_of, O_src in Hr |- *. cbn [ob_base ob_lo ob_hi fst snd] in Hr |- *. exact Hr.
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) is_srcX (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
    + intros r a Hr Hb Ha. unfold is_srcX in Hb. apply lazy_andb_prop in Hb as [H1 H2]. apply sv_eqb_sound in H1. apply sv_eqb_sound in H2.
      left. apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HT). apply SP. destruct r as [rb rl]. cbn [fst snd] in H1, H2, Ha. subst. exact Ha.
    + exact I.
  - change (wsub_get s_m 12) with (e32 vK). factz HF (SPUle (SLit 65536) vK) H1. factz HF (SPUle vK (SLit (2 ^ 32 + 16))) H2.
    rewrite !uval_lit in H1, H2 by lia. unfold e32. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma X_E_m : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z42S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S76A1S55R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (malloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp ndKc bd_m (FAM b tp0) CMALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull ndM (65, z0)); [innth 4 | meas].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok ndMok (65, z0)); [innth 5 | meas]].
    intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). vm_compute. reflexivity.
Qed.

Lemma used_new_val : ltac2:(tb__ "0|0|
SbS0S48Q40A1S19R1S4dA2S19R1S97A2A3Fr;").
Proof.
  intros r. reflexivity.
Qed.

Lemma X_X_sret : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z33S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S8eA1S72R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndL) C_loop rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_sret X_sret1 tp _ X_sret1_eq Hw) as H1.
    pose proof (AxCellA.SPA_recellv segs _ rho X_sret1 iH jU vSZ (fst rcU) (snd rcU) tp _ ltac:(rewrite rcU_eq; destruct rcU; reflexivity)
                  ltac:(vm_compute; reflexivity) (fun _ => used_new_val rho) H1) as H1r.
    rewrite X_sret1r_eq in H1r.
    pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m bd_m2 0 blkN vHD vK vSZ
                  X_sret1r objsN ohN otN rho tp tr ms md objsN_eq eq_refl) as H2.
    specialize (H2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) H1r).
    rewrite X_sret2_eq in H2. cbn [remove_nth fst blkN] in H2.
    set (rho1 := rho_absorb rho [otN] (vms md tp ms)) in H2.
    assert (HF1 : Forall (holds rho1) (ss_facts (ax_S X_sret2))) by exact (smatchA_facts segs _ _ _ _ (proj1 H2)).
    assert (SZ1 : srcz rho1) by srcz_tac HF1.
    factz HF1 (SPUle (SAlu ALU_ADD (SVar pN) (e32 vK)) (SVar 30)) HE1. factz HF1 (SPUle (SVar pN) (SVar 30)) HE2.
    factz HF1 (SPUle (SLit 65536) vK) HK1. factz HF1 (SPUle vK (SLit (2 ^ 32 + 16))) HK2. factz HF1 (SPUle (SAlu ALU_ADD vSZ (SLit 16)) vK) HK3.
    factz HF1 (SPUle (SVar 30) (SLit 140737479966720)) HT30. rewrite !uval_lit in HT30, HK1, HK2 by lia.
    pose proof (uval_range rho1 (SVar pN)) as RP. pose proof (uval_range rho1 vK) as RK.
    assert (EK : uval rho1 (e32 vK) = uval rho1 vK + 32) by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small in HE1 by (rewrite EK; lia). rewrite EK in HE1.
    rewrite uval_add_small in HK3 by (rewrite uval_lit by lia; destruct SZ1; lia). rewrite uval_lit in HK3 by lia.
    assert (EPn : uval rho1 p_new = uval rho1 (SVar pN) + 32) by (unfold p_new; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    assert (H3 : SPA segs (JAv (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD vK [(p_new, vSZ)]))) X_sret3 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_sret3_eq.
      apply (SPA_refacts_JA segs _ rho1 (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2))); [| vm_compute; reflexivity |].
      - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_m2 (SVar pN) vHD vK p_new vSZ X_sret2 rho1 tp _);
          [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact H2].
        + intros r HFr. assert (SZr : srcz r) by srcz_tac HFr.
          factz HFr (SPUle (SAlu ALU_ADD vSZ (SLit 16)) vK) HK3'. factz HFr (SPUle vK (SLit (2 ^ 32 + 16))) HK2'. rewrite uval_lit in HK2' by lia.
          rewrite uval_add_small in HK3' by (rewrite uval_lit by lia; destruct SZr; lia). rewrite uval_lit in HK3' by lia.
          pose proof (uval_range r (SVar pN)). unfold p_new.
          rewrite uval_add_small by (rewrite uval_lit by lia; factz HFr (SPUle (SVar pN) (SVar 30)) HE; factz HFr (SPUle (SVar 30) (SLit 140737479966720)) HT30'; rewrite uval_lit in HT30' by lia; lia).
          rewrite uval_lit by lia. destruct SZr. lia.
        + intros Ai rho2 tp2 md2 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho1 Hav eq_refl) as ET. split.
          * intros o a Ho Hr. rewrite objsN2_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
            -- destruct (objs_ok_ad rho1 objsN ltac:(basez_tac HF') SZ1 (srcP_of rho1 HP0 Hav)
                          ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 12)
                          ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
            -- right; right. unfold ohN in Hr. apply range_lit' in Hr; [|lia|lia]. unfold pN. lia.
          * intros r a Hr Ha.
            assert (HX : In r [(vAR, SLit 64); (vSRC, vLS); (SVar pN, e32 vK)]) by exact Hr. clear Hr.
            pose proof (AAP.basez_of rho1 _ HF' ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
            destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
            -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *. lia.
            -- destruct SZ1 as [_ _ [S1 S2] ST]. lia.
            -- rewrite EK in Ha. lia.
      - intros tr' md' _ HF2. apply Forall_app. split; [|exact HF2].
        unfold new_facts. destruct SZ1. change (bv_unsigned (rw rho1 V_TOP)) with (uval rho1 (SVar 30)) in *.
        assert (EPS : uval rho1 (SAlu ALU_ADD p_new vSZ) = uval rho1 p_new + uval rho1 vSZ) by (rewrite uval_add_small by lia; lia).
        assert (EHC : uval rho1 (SAlu ALU_ADD (SVar pN) (e32 vK)) = uval rho1 (SVar pN) + (uval rho1 vK + 32)) by (rewrite uval_add_small by (rewrite EK; lia); rewrite EK; lia).
        repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
          rewrite ?EPS, ?EHC, ?EPn; rewrite ?uval_lit by lia; lia. }
    exists (rho_sub rho1 s_sret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_sret3 C_loop s_sret (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD vK [(p_new, vSZ)])) ndL);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
  apply TR_exw. intros rho'. apply (REENTER C_loop ndL (50, SAlu ALU_SUB vSZ vI)); [innth 6 | meas].
Qed.

Lemma X_X_ret : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S8dA1S71R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndK) P_ok rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_ret X_ret1 tp _ X_ret1_eq Hw) as H1.
    pose proof (JA_unslot segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HNP tv0 [] bd_loop vH vNXl vCAPl vP vSZ
                  X_ret1 (objsR ++ [ohR]) osR rho tp tr ms md objsR_eq ltac:(vm_compute; reflexivity) H1) as H2.
    rewrite X_ret2_eq in H2. set (rho1 := rho_absorb rho [osR] (vms md tp ms)) in H2.
    pose proof (JA_close segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_loop [] vH vNXl vCAPl vUc
                  X_ret2 objsR ohR rho1 tp tr ms md objsR2_eq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; left; reflexivity) eq_refl ltac:(vm_compute; reflexivity) H2) as H3.
    rewrite X_ret3_eq in H3. set (rho2 := rho_absorb rho1 [ohR] (vms md tp ms)) in H3.
    exists (rho_sub rho2 s_ret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_ret3 P_ok s_ret (NDA tv0 [] [] (AHead vH true)) ndK);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
  apply TR_exw. intros rho'. apply X_P_ok.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S5S9dS31S4SdA2M0SbS2cS48Q40A1A1M1G1S9aS31S31S5S9dA2M2G0A2S32G2G0S32S5S9dR6R5A4R4A4S75A3VTR;S4aS29VJAv;R6A1R7R4R3A5VFAM;Sa2S32G2G0S32S5S9dR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_open. meas.
  - apply X_X_nohead. meas.
  - apply X_X_nofitO.
  - apply X_X_fit. meas.
  - apply X_X_nofit. meas.
  - apply X_X_K1. meas.
  - apply X_X_K2. meas.
  - apply X_E_m. meas.
  - apply X_X_sret. meas.
  - apply X_X_ret.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
SabS29VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sc2S29Sb9VAInv;VCST;VXGL;A5").

Theorem arena_dup_sum : ltac2:(tb__ "0|0|
S2cS48Q40A1A1Sb7S29Vok;S4aS29Sa1VAInv;VCST;VXGL;VKc;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eS5aAaS6dVrho0;R1A5Sb0S29S9cVrho0;R1Sd4A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc ALA FUEL_ad cutpcs_ad 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertA_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_false segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok))
         with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_ad CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_ad P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sc3S29Sb9VAInv;VCST;VXGL;A5").

Theorem arena_dup_sum_ex : ltac2:(tb__ "0|0|
S2cS48Q40A1A1Sb6S29S4aS29Sa1VAInv;VCST;VXGL;VKc;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eS5aAaS6dVrho0;R1A5Sb0S29S9cVrho0;R1Sd4A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc ALA FUEL_ad cutpcs_ad 100 cutsE exitsE (Q tp0) ejcertA_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_false segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_ad CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_ad P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_finalize_shape_dup1_pf.

(* [comment removed for export] *)
Module Lib_finalize_shape_dup2_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sprop"; "sv"; "SLit"; "SPUle"; "sprop_eqb"; "SAlu"; "ss_facts"; "SVar"; "ss_objs"; "sv_eqb"; "holds"; "ss_next"; "cell"; "eval"; "ob_base"; "ob_hi"; "ob_lo"; "sstate"; "DUnknown"; "ob_dflt"; "obj_range"; "odefault"; "rw"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "mul"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "O_got"; "O_rtc"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "true"; "nil"; "prod"; "pair"; "app"; "Some"; "fst"; "option"; "false"; "snd"; "None"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BI"; "batom"; "ASv"; "KU"; "bsumK"; "bsumV"; "bd_nn"; "bd_subst"; "bd_wpos"; "bud_le"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup2"; "vSZ"; "vCAP"; "vHD"; "vLS"; "vSRC"; "s_m"; "tv0"; "vU"; "E_m"; "R_m"; "X_fit"; "X_sret2"; "bd_slow"; "nd0"; "objsR"; "P_fail"; "P_ok"; "X_ret1"; "X_ret2"; "X_sret1"; "X_sret1r"; "am_np"; "ndF"; "ndK"; "ndO"; "ndS"; "objsN"; "ohN"; "ohR"; "p_fit"; "vUg"; "O_src"; "Pre_ad"; "Pre_m"; "X_nofit1"; "X_open"; "X_ret"; "X_sret"; "base_fit"; "cutsE"; "exitsE"; "ndKc"; "rcU"; "sel_sret"; "C_K"; "C_open"; "FUEL_ad"; "O_W"; "T_mnull"; "T_mok0"; "X_K1"; "X_K2"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_nohead"; "X_ret3"; "X_sret3"; "bd_K"; "cutpcs_ad"; "fit_facts"; "iH"; "jU"; "ndL"; "ndMok"; "new_facts"; "nofit_fact"; "osR"; "otN"; "p_new"; "pad_fit"; "sel_ret"; "used_fit"; "used_new"; "vAR"; "@Stdlib.Lists.List"; "existsb"; "In"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "potK"; "potV"; "JA_pre"; "emeasA"; "JA"; "JLA"; "NDA"; "am_eqb"; "am_subst"; "ejcertA"; "nd_below"; "nodeIA"; "ok_frameKA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_shape_dup2_pf"; "P0_ad"; "ohF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "J_alloc_pre"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_malloc"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXSplit"; "@Corelib.Lists.ListDef"; "Forall"; "map";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_shape_dup2_pf.Sum"; "Posts_ad"; "srcz"; "JL"; "srcF"; "srcP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "FFx"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "POT"; "drop_lastA"; "carve_stateA"; "e32"; "open_stateA"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_shape_dup2_pf.AAP"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_shape_dup2_pf.Sum.X"; "openF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T0"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxCellA"; "recellv_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup2.
Module AAP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_arena_alloc_pf. End AAP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ADAddr RA.ReallocAddr.
Local Open Scope lazy_bool_scope.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S0S2dSa8S29S9cS7bS89P64S74S75A7S2fA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C_open_eq : ltac2:(tb__ "0|0|
S0S5Se2S70S4fA2S7aA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S0S5Se7S6eS55S52S56SbdSb9S30SbbA1SbaA3A5S7dA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S0S5Se7S6eS55S52S56SbeSb9S30SbbA1SbaA3A5S7eA3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S0S5SddS6fS2eScS90S12S6S6fA1A1A3A2S83A3"). Proof. vm_compute. reflexivity. Qed.
Definition ohF : sobj := Eval vm_compute in last (ss_objs (ax_S X_fit)) O_src.
Lemma objsF_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S57A1A1M0S33SaS9bSaG0A2S2eSaSaeS30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_fit3_eq : ltac2:(tb__ "0|0|
S0S5SddSe0S57S6aS4dA3S33ScS8aS12S6S57A1A1A3A2S81A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret1_eq : ltac2:(tb__ "0|0|
S0S36S5A1ScdS72S2eScbSccS78A1S2eScbSceSecS3aS3bS78A2U1A2SeZ18A1A2S30ScbA1A3A3A2S34S5S60A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma rcU_eq : ltac2:(tb__ "0|1|
S0S36S31S1dS18A2M0A1Sf3S6S60A1S8bS8cS4dA4S34G0S77A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret1r_eq : ltac2:(tb__ "0|0|
S0S5S8S60S35S1dS18S77A3A2S61A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsN_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S61A1A1S33SaS33SaS67S2eSaS68S30SaA1M0A3A3S2eSaS92G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret2_eq : ltac2:(tb__ "0|0|
S0S5SdfS61S33SaS67S2eSaS68S30SaA1A3A3A2S58A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsN2_eq : ltac2:(tb__ "0|0|
S0S2cSaA1S14S6S58A1A1S33SaS67S2eSaS68S30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret3_eq : ltac2:(tb__ "0|0|
S0S5SddSe0S58S93S4dA3S33ScS8fS12S6S58A1A1A3A2S87A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret1_eq : ltac2:(tb__ "0|0|
S0S36S5A1ScdS71S2eScbSccS95A1S30ScbA1A3A2S34S5S5eA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S5eA1A1S33SaS33SaS5bS2eSaS69S30SaA1M0A3A3S2eSaS91G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret2_eq : ltac2:(tb__ "0|0|
S0S5SdfS5eS33SaS5bS2eSaS69S30SaA1A3A3A2S5fA3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR2_eq : ltac2:(tb__ "0|0|
S0S2cSaA1S14S6S5fA1A1S33SaS5bS2eSaS69S30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret3_eq : ltac2:(tb__ "0|0|
S0S5SdfS5fS5bA2S86A3"). Proof. vm_compute. reflexivity. Qed.

Definition P0_ad (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S4S1S23S3cVr;S51A2M0R1A2S27R1S24G0S3cVr;S50A2A2A2A2Sd9VCST;Vr;VFB;VFF;R2A5F_;Fa;").

Definition is_src (o : sobj) : bool := ltac2:(tb__ "0|1|
S2dS2dL_;M0S15S1aVo;A1S51A2G0S15S1cVo;A1SeZ0A1A2S15S1bVo;A1S50A2S37X2dx2S37X2dx2").
Definition is_srcX (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S2dS2dL_;S15S35SdSdVr;A3S51A2S15S38SdSdVr;A3S50A2S37X2dx2").

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Variable AInv : ltac2:(tb__ "0|0|
Se4SbS2cS48Q40A1A1Sd2OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sc4S29VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S4SebVCST;R1A2S1S23Z0R2A2S27R2SeaA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S4SebVXGL;R1A2S1S23Z0R2A2S27R2SeaA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2cS31S31S4S4A2S4A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
Sa4VAInv;VCST;VXGL;VKc;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eVnd;Aa").
Definition Posts_ad : list (axst * jpostA) := ltac2:(tb__ "0|1|
S2eS31S5SafA2M0S32S5SafS5cSd6S63A1A4S2eG0S32S5SafS5dSd6S64A1A4S30G0A1A3A3").

Definition PD_ad : list (axst * ndesc) := ltac2:(tb__ "0|1|
S2eS31S5S9dA2M0S32S5S9dS5cS63A4S2eG0S32S5S9dS5dS64A4S30G0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
Sa3VAInv;VCST;VXGL;S9cVKc;Vrho0;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S31S5S9dA2SefFn;") := ltac2:(tb__ "0|0|
SaaVAInv;VCST;VXGL;S9cVKc;Vrho0;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sb0S29S9cVrho0;Vtp0;Sd4A5").

Definition srcF (F : list sprop) : Prop := ltac2:(tb__ "0|1|
S1S0S2dS99ScS10SfSeZ1A1S4dA2A1VF;A3S2fA3S1S0S2dS99ScS10SfS4dS50A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS50SeS25Z2Z20A2A1A2A1VF;A3S2fA3S1S0S2dS99ScS10SfSeZ1000A1S51A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS11SacS51S50A3S13P1eA1M0A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS51G0A2A1VF;A3S2fA3S0S2dS99ScS10SfG0SeZ7fffff800000A1A2A1VF;A3S2fA3A2A2A2A2A2A2").
Record srcz (rho : valuation) : Prop := SZ_ {
  sz_n : 1 <= uval rho vSZ <= uval rho vLS; sz_L : uval rho vLS <= 2 ^ 32;
  sz_src : 4096 <= uval rho vSRC /\ uval rho vSRC + uval rho vLS <= bv_unsigned (rw rho V_TOP);
  sz_top : bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma srcz_of : ltac2:(tb__ "0|0|
SbS2cScA1ScfScS16R2A1R1A3Sd7R2A1Sd5R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & BT).
  pose proof (holds_mem _ _ _ HF BT) as HT2. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  rewrite !uval_lit in H1, H3, H4, HT2 by lia.
  rewrite uval_add_small in H5 by (pose proof (uval_range rho vSRC); pose proof (uval_range rho vLS); lia).
  constructor; lia.
Qed.
Ltac basez_tac HF := exact (AAP.basez_of _ _ HF ltac:(repeat split; vm_compute; reflexivity)).
Ltac srcz_tac HF := exact (srcz_of _ _ HF ltac:(repeat split; vm_compute; reflexivity)).

Definition srcP (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S4S1S23S3cVrho;S51A2M0R1A2S27R1S24G0S3cVrho;S50A2A2A2A2Sd9VCST;Vrho0;VFB;VFF;R2A5F_;Fa;").
Lemma srcP_of : ltac2:(tb__ "0|0|
SbSadVCST;VFB;VFF;Vrho0;A4Se5S9cVrho0;R2A3Sd8R3A1F_;F_;Frho;").
Proof.
  intros rho HP [Hav _] a Ha. apply HP. unfold uval in *. cbn [eval vSRC vLS] in *.
  rewrite (Hav 13%positive) by reflexivity. rewrite (Hav 16%positive) by reflexivity. exact Ha.
Qed.
Lemma src_range : ltac2:(tb__ "0|2|
SbS4Sd5R2A1S1S23S35S4S4S20R3S6cA2M0A3R2A2S27R2S38S4S4G0A3A2A2S1S23S3cR4S51A2M1R3A2S27R3S24G1S3cR4S50A2A2A2A2F_;F_;Fa;Frho;").
Proof.
  intros rho a SZ Hr. destruct SZ as [S1 S2 S3 S4]. unfold obj_range, obj_lo_of, obj_hi_of, O_src in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite (soff_smallu rho vLS) in Hr by lia. unfold uval in *. lia.
Qed.
Lemma pclMA_x : ltac2:(tb__ "0|0|
SbS4Sd9VCST;Vrho0;VFB;VFF;R1A5Sd9VCST;Vrho0;Sf0VFB;R3S53A3SdaVFF;R3S30S31S31SdS4A2SdA2A1A3R2A5F_;Fa;Frho;").
Proof.
  intros rho a [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | exact Hr].
  - right; right; right. exists f, s, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin | exact Hr].
Qed.

Lemma objs_ok_ad : ltac2:(tb__ "0|5|
SbS2cSaA1SedR2A1Sd5R3A1Sd8R4A1SaS9aSaR1R5A3S2S1S0SdS1aR2A1M0S13PaA1A3S1S0SdS1cR2A1M1SeN40A1A3S1S0SdS1bR2A1M2SeZ0A1M3A3S0S21S1fR2A1S1eA3M4A2A2A2S2S0SaR2S7cA3S2S1S0SdG0S98A3S1S0SdG1G3A3S1S0SdG2SeZ40A1A3G4A2A2A2S2S2S0SaR2S2aA3S0SaR2S2bA3A2S0SaR2S6cA3A2A2A2A2F_;Fo;S0S4Sf1Vrho0;A1S49Q40S22R6Sc1A2A2A3Se3VCST;Vrho0;VFB;VFF;R7S53S30S31S31SdS4A2SdA2A1R6A8F_;F_;F_;F_;F_;Fobjs;Frho;").
Proof.
  intros rho objs BZ SZ SP Hcls ET o a Ho Hr.
  destruct (Hcls o Ho) as [C|[C|[C|[C| ->]]]].
  1-4: refine (AAP.objs_ok_gen CST FB FF rho0 rho [o] BZ _ ET o a (or_introl eq_refl) Hr); intros o' [<-|[]]; auto 10.
  left. apply pclMA_x. apply SP. exact (src_range rho a SZ Hr).
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S4S2cS48Q40A1A1Sb4F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4bS5SbS2cS48Q40A1A1Sb4ScfScS16R3A1S12S6R4A1A1A3VTR;S4aS29R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sb4Sb4Sb4Sb5R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
Sb4Sb4Sb5S3R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S4bS4bS5S5Sc8S2cSaA1M0S2cS31S5SafA2M1A1S2cS31SdSdA2M2A1Sb4SbS2cS48Q40A1A1M3G2S9aG2R1R5A3S9aG2R2S7RbA1A3F_;Fr;S0S36G0A1Sb3RaR9R8A3S34G0R7A2A3S0S2dSb2RbRaR9R8Sd0G1S5S35S5SafA2R7A4A5S2fA3SbG3VTR;S4aS29RfRdR2R1A5Sb0S29S17S6RdA1A1R2R1RaA5A2Ftp1;Frho1;S2cSd3A1M4Sd1Sd2S4cS29R9R8R10S32G4SdbR3SdcR2R1A2A4A5R13RaR9R4R2A4R13Sc7Sc6RbRfSb8R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S5SafG4Sd1Sd2SbG3G4Sd1Sd2S9aG1S32S5SafRaR9A4R14A3S4cS29R12R11R19S32G4SdbR9SdcR8R7A2A4A5R1cR13R12RaR8A4Se5S17S6R1aA1A1Sc7Sc6R14R18Sb8R9R13RaA3A3R19A2R8A3S4cS29R9R8ReS32G4SdbR7SdcR6R5A2A4A5ReSc7Sc6R16R1aSb8RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sf4R17Sb8RcR16RdA3R1bR1cR1dR10R1eR19RbA9SbSe6R18Sb8RdR17ReA3R1cR1dS6R1eA1S6R1fA1S6R11A1R1RcA9VTR;S4aS29Sb1R11Sc7Sc6R19R1dSb8ReR18RfA3A3R1eA2R18RdRcA5Sf5R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S4aS29R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Se4SbS2cS48Q40A1A1VTR;S4aS29SbcVAInv;S30SbbA1M0SbaR3VKc;S13PcA1A6Sc0Sb9G0SbaA3R2R1A5Sb0S29S9cR2R1SbfSb9VAInv;VCST;VXGL;G0SbaR3VKc;A8A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S5S9dS31S4SdA2M0SbS2cS48Q40A1A1M1S4G1S9aS31S31S5S9dA2M2G0A2S32G2G0S32S5S9dR7R6A4R5A4S74A3S1S23Z0Sa2S32G2G0S32S5S9dR8R7A4R6A4R5A2M3A2S27G3R3A2A2VTR;S4aS29VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S5S9dSbS2cS48Q40A1A1M0S4G0S9aS31S5SafA2S32S5SafR6Sd6R5A1A4Sd4A3VTR;S4aS29VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd];
  match goal with |- context [bv_unsigned (eval ?r ?e)] => pose proof (U_range (eval r e)) end; unfold M64v in *; lia.
Tactic Notation "innth" integer(k) := do k right; left; reflexivity.

Lemma X_P_fail : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S63A1S5cR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. left. reflexivity. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S64A1S5dR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. right. left. reflexivity. Qed.

Lemma X_X_open : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z5bS25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S5aA1S70R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndO) C_open rho' tp w)).
  { intros w Hw.
    destruct (JA_open segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] CH vHD true X_open rho tp w) as (rho' & _ & Hw');
      [vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | exact Hw |].
    - intros Ai rho1 tp1 md1 HF HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. split.
      + apply objs_ok_ad; [basez_tac HF | srcz_tac HF | exact (srcP_of rho HP0 Hav) | | exact ET].
        intros o Ho. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 10.
      + intros r a Hr Ha. assert (HX : In r [(vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
        pose proof (srcz_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [S1 S2] ST].
        destruct HX as [<-|[<-|[]]]; cbn [fst snd] in Ha; [rewrite uval_lit in Ha by lia; unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *; lia | lia].
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER C_open ndO (90, z0)); [innth 1 | meas].
Qed.

Lemma X_X_nohead : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z51S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S5aA1S85R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_slow ndS (80, z0) (rho_sub rho s_nohead)); [innth 2 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv0 [] (CH ++ [BIc 1 0 AV0; BIc 0 1 AK0]) (AHead vHD false)) ndS);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  apply (JA_pot_out0 segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HBX); [vm_compute; reflexivity | exact Hw].
Qed.

Lemma and16_eq : and_hmask 18446744073709551600 = Some 16. Proof. vm_compute. reflexivity. Qed.
Lemma fit_arith : ltac2:(tb__ "0|c|
SbS23S3cR1S4fA2Z7fffff800000A2S23S3cR2S54A2S3cR2S4eA2A2S23S3cR3S4eA2S28S25Z2M0Z28A2Z21A2A2S23S3cR4S4dA2S25G0Z20M1A2A2S1S0S4S3cR5S73A2M2S24S24S3cR5S4fA2M3G1A2M4S3cR5S54A2M5A2A3S1S1S23G2S3cR5S6aA2M6A2S23G6S24G2ZfM7A2M8A2A2S1S0S4S3cR5S94A2M9S28G6G2A2A3S1S0S4S3cR5S96A2S24S24G5S3cR5S4dA2MaA2G9A2A3S1S0S4S3cR5S11SacS73SeG7A1MbA3A2G8A3S1S0S4S3cR5S11SacS6aS4dA3A2S24G6GaA2A3S1S0S4S3cR5S11SacS4fSe1S4eA1A3A2S24G3S24S3cR5S4eA2G1A2A2A3S1S0S4S3cR5S11SacS54S11SacS4dGbA3A3A2S24G5S24GaG7A2A2A3S0S4S3cR5S11SacS4fSeG1A1A3A2G4A3A2A2A2A2A2A2A2A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho Hh Hu Hc Hn.
  pose proof (uval_range rho vHD) as R1. pose proof (uval_range rho vU) as R2. pose proof (uval_range rho vCAP) as R3. pose proof (uval_range rho vSZ) as R4.
  assert (EB : uval rho base_fit = uval rho vHD + 32 + uval rho vU).
  { unfold base_fit. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (E15 : uval rho (SAlu ALU_ADD base_fit (SLit 15)) = uval rho base_fit + 15).
  { rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (EP : uval rho base_fit <= uval rho p_fit <= uval rho base_fit + 15).
  { assert (Ep : p_fit = SAlu ALU_AND (SAlu ALU_ADD base_fit (SLit 15)) (SLit 18446744073709551600)) by reflexivity. rewrite Ep.
    unfold uval at 2 3. rewrite (U_and_hmask rho _ _ 16 and16_eq). change (bv_unsigned (eval rho (SAlu ALU_ADD base_fit (SLit 15)))) with (uval rho (SAlu ALU_ADD base_fit (SLit 15))).
    rewrite E15. pose proof (Z.mod_pos_bound (uval rho base_fit + 15) 16 ltac:(lia)). lia. }
  assert (EPAD : uval rho pad_fit = uval rho p_fit - uval rho base_fit).
  { unfold pad_fit. unfold uval at 1. rewrite U_sub. change (bv_unsigned (eval rho p_fit)) with (uval rho p_fit). change (bv_unsigned (eval rho base_fit)) with (uval rho base_fit).
    unfold M64v. apply Z.mod_small. lia. }
  assert (E1 : uval rho (SAlu ALU_ADD pad_fit vSZ) = uval rho pad_fit + uval rho vSZ) by (rewrite uval_add_small by (rewrite EPAD; lia); lia).
  split; [exact EB|]. split; [exact EP|]. split; [exact EPAD|]. split; [|split; [exact E15|split; [|split; [|split]]]].
  - unfold used_fit. rewrite uval_add_small by (rewrite E1, EPAD; lia). rewrite E1. lia.
  - rewrite uval_add_small by lia. reflexivity.
  - unfold e32. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
  - rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
  - rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
Qed.

Definition openF (F : list sprop) : Prop := ltac2:(tb__ "0|1|
S1S0S2dS99ScS10SfS4fS13P1eA1M0A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS54S4eA2A1VF;A3S2fA3S1S0S2dS99ScS10SfS4eSeS28S25Z2Z28A2Z21A2A1A2A1VF;A3S2fA3S1S0S2dS99ScS10SfSeZ10000A1S4eA2A1VF;A3S2fA3S1S0S2dS99ScS10SfS11SacS4fSe1S4eA1A3G0A2A1VF;A3S2fA3S1S0S2dS99ScS10SfSeZ1000A1S4fA2A1VF;A3S2fA3S0S2dS99ScS10SfG0SeZ7fffff800000A1A2A1VF;A3S2fA3A2A2A2A2A2A2").
Lemma openz : ltac2:(tb__ "0|6|
SbS2cScA1ScfScS16R2A1R1A3SeeR2A1S23S3cR4S4dA2S25Z2M0Z20M1A2A2S1S23S3cR5S4fA2M2Z7fffff800000M3A2S1S23S3cR5S54A2S3cR5S4eA2M4A2S1S23G4S28S25G0Z28A2Z21A2A2S1S23Z10000G4A2S1S23S24G2S24G4G1A2A2S3cR5S13P1eA1A2M5A2S1S23Z1000G2A2S23G5G3A2A2A2A2A2A2A2F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & BT) Hn.
  pose proof (holds_mem _ _ _ HF BT) as HT2. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  rewrite !uval_lit in H3, H4, H6, HT2 by lia.
  destruct (fit_arith rho ltac:(lia) H2 H3 Hn) as (_ & _ & _ & _ & _ & _ & E7 & _). rewrite E7 in H5. lia.
Qed.
Ltac openz_tac HF SZ := exact (openz _ _ HF ltac:(repeat split; vm_compute; reflexivity) ltac:(destruct SZ; lia)).

Lemma X_X_nofitO : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S65A1S84R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF. apply TR_false. intros w _.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & _).
  factz HF (SPBranch BC_LTU (SAlu ALU_XOR vSZ (SLit 18446744073709551615)) pad_fit) H0.
  assert (EX : uval rho (SAlu ALU_XOR vSZ (SLit 18446744073709551615)) = 2 ^ 64 - 1 - uval rho vSZ).
  { unfold uval. rewrite (U_xor_m1 rho vSZ 18446744073709551615 ltac:(reflexivity)). reflexivity. }
  rewrite EX in H0. destruct SZ. lia.
Qed.

Lemma X_X_nofit : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z51S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S65A1S82R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & EN & _).
  factz HF (SPNot (SPBranch BC_GEU vCAP used_fit)) H0. rewrite EN in H0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndS) C_slow rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (JA_close_np segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_open vHD vNX vCAP vU X_nofit
                  (removelast (ss_objs (ax_S X_nofit))) (AA.O_hdr vHD vNX vCAP vU) rho tp tr ms md) as CL.
    specialize (CL ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; left; reflexivity) eq_refl Hw).
    set (rho1 := rho_absorb rho [AA.O_hdr vHD vNX vCAP vU] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv0 [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. change (drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit)))) with X_nofit1 in CL.
      apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | vm_compute; reflexivity |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65537 mod M64v) with 65537.
      assert (EU : forall e, eval rho1 e = eval rho e) by (intros e; unfold rho1; apply eval_absorb).
      rewrite EU. change (bv_unsigned (eval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16))))) with (uval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16)))).
      destruct SZ as [S1 S2 S3 S4]. pose proof (uval_range rho vU).
      rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
      rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
    exists (rho_sub rho1 s_nofit).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv0 [] bd_open am_np) ndS);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact CL2]. }
  apply TR_exw. intros rho'. apply (REENTER C_slow ndS (80, z0)); [innth 2 | meas].
Qed.

Lemma X_X_fit : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z33S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S65A1S57R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & EN & E15 & E72 & EHC & EU15 & EH32).
  factz HF (SPBranch BC_GEU vCAP used_fit) H0. rewrite EN in H0.
  eapply TR_pre; [|apply (REENTER C_loop ndL (50, SAlu ALU_SUB vSZ vI) (rho_sub rho s_fit)); [innth 6 | meas]].
  intros w Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_fit3 C_loop s_fit (NDA tv0 [] bd_open (AOpen vHD vNX vCAP [(p_fit, vSZ)])) ndL);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  rewrite <- X_fit3_eq. apply (SPA_refacts_JA segs _ rho (carve_stateA X_fit p_fit vSZ) (fit_facts ++ ss_facts (ax_S X_fit))); [| vm_compute; reflexivity |].
  - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_open vHD vNX vCAP p_fit vSZ X_fit rho tp w);
      [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact Hw].
    + intros r HFr. assert (SZr : srcz r) by srcz_tac HFr.
      assert (OZr : uval r vHD <= 140737479966720 /\ uval r vU <= uval r vCAP /\ uval r vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval r vCAP
                    /\ uval r vHD + (uval r vCAP + 32) <= uval r (SVar 30) /\ 4096 <= uval r vHD /\ uval r (SVar 30) <= 140737479966720) by openz_tac HFr SZr.
      destruct OZr as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
      destruct (fit_arith r Y1 Y2 Y3 ltac:(destruct SZr; lia)) as (EB' & EP' & EPAD' & EN' & _).
      factz HFr (SPBranch BC_GEU vCAP used_fit) H1. rewrite EN' in H1. pose proof (uval_range r vU). destruct SZr. lia.
    + intros Ai rho1 tp1 md1 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. split.
      * intros o a Ho Hr. rewrite objsF_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
        -- destruct (objs_ok_ad rho (removelast (ss_objs (ax_S X_fit))) ltac:(basez_tac HF) SZ (srcP_of rho HP0 Hav)
                      ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 12)
                      ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
        -- right; right. unfold ohF in Hr. apply range_lit' in Hr; [|lia|lia]. unfold vHD, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vHD. lia.
      * intros r a Hr Ha.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
        assert (HX : In r [(vHD, e32 vCAP); (vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
        -- unfold e32 in Ha. rewrite uval_add_small in Ha by (rewrite uval_lit by lia; lia). rewrite uval_lit in Ha by lia.
           pose proof (uval_range rho vHD). lia.
        -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *. lia.
        -- destruct SZ as [_ _ [S1 S2] ST]. lia.
  - intros tr md _ HF2. apply Forall_app. split; [|exact HF2].
    unfold fit_facts. pose proof (uval_range rho vU). pose proof (uval_range rho vHD). destruct SZ.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
      rewrite ?E15, ?E72, ?EHC, ?EU15, ?EH32, ?EN; rewrite ?uval_lit by lia; lia.
Qed.

Lemma sums_slow : ltac2:(tb__ "0|2|
SbS1S0S4S43S59R1A2S24Sa0S3cR1S6bA2M0A1S24S26Z2S3cR1S4dA2M1A2Z60A2A2A3S0S4S42S59R1A2S24S9fG0A1S24S26Z4G1A2Z40A2A2A3A2Fr;").
Proof.
  intros r. unfold bd_slow. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vUg) as (-> & -> & _).
  unfold CH. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. lia.
Qed.
Lemma sums_K : ltac2:(tb__ "0|7|
SbSdS1S0S4S43S33S3dS2eS3dS3eZ1M0Z0M1S2eS31S4S3fA2M2S32S4S3fG0S40R1A1A4S30G2A1M3A3G1A4S2eS3dS3eG1G0G3S26Z2S41A2M4A4S30S3dA1A3A3SdeS4dA1A3M5R2A2S24S3cR2R1A2Sa0S3cR2S4dA2M6A1A2A3S1S0S4S42G5R2A2S24G4S9fG6A1A2A3S1S44G5R2A2S0S2dS46G5A1S2fA3A2A2A2Fk;Fr;").
Proof.
  intros r k. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vSZ) as (-> & -> & NN & WP).
  cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. pose proof (uval_range r k). unfold KU.
  split; [lia|]. split; [lia|]. split; [|reflexivity].
  apply bd_nn_app. split; [|exact NN]. repeat constructor; unfold bival; cbn [lfval aval bi_f bi_c]; lia.
Qed.

Lemma pay_K_arith : ltac2:(tb__ "0|5|
S4S4S4S23Z0R3A2S1S23Z1R3A2S23R3S25Z2M0Z20M1A2A2A2S23Z10001S24S24R5R4A2Z10M2A2A2S2S1S0S4R4Z10000M3A3S27S24R5G2A2M4G3A2A2S1S0S4R4G4A3S23G3G4A2A2A2S1S23S24S24R5G1A2Sa0R6A1A2S24Sa0R7A1S24S26G0R6A2Z60A2A2A2S23S24S26G0S41A2S9fR6A1A2S24S9fR7A1S24S26Z4R6A2Z40A2A2A2A2F_;F_;F_;F_;Fk;Fn;Fug;").
Proof. intros ug n k Hu Hn Hs Hk. unfold potV, potK, AV0, AK0, KU. destruct Hk as [[-> Hc]|[-> Hc]]; split; lia. Qed.

Lemma pay_K : ltac2:(tb__ "0|b|
S5SdSd7S12S6R2A1A1A1S0S2dS99ScS10SfSeZ10001A1S11SacS6bS11SacS4dSeZ10M0A1A3A3A2A1S12S6R3A1A1A3S2fA3S0S2dS99ScS10SfS6bSeS25Z2M1Z28A2A1A2A1S12S6R4A1A1A3S2fA3SbScfScS16R1A1S12S6R6A1A1M2A3Sd5R2A1S2S1S0S4S3cR3R7A2M3Z10020A3S27S24S3cR3S4dA2M4G0A2M5Z10000M6A2A2S1S0S4G3S24G4Z30A2A3S23G6G5A2A2A2F_;F_;Fr;Se8S9cVrho0;SadVCST;VFB;VFF;A3G2SeZ0M7A1G7S59S33S3dS2eS3dS3eZ1M8G7S2eS31S4S3fA2M9S32S4S3fG8S40R5A1A4S30G9A1MaA3G7A4S2eS3dS3eG7G8GaS26G1S41A2A4S30S3dA1A3A3SdeS4dA1A3A8F_;F_;F_;F_;Fk;FX;").
Proof.
  intros X k HB Hug1 Hug2 HK. destruct (sums_K rho0 k) as (_ & _ & _ & WP). split; [exact WP|]. split; [lia|]. intros r HF _ _ _. unfold pay_sem.
  assert (SZ : srcz r) by exact (srcz_of _ _ HF HB).
  destruct (sums_K r k) as (-> & -> & NN & _). destruct (sums_slow r) as [-> ->]. rewrite uval_lit by lia.
  pose proof (holds_mem _ _ _ HF Hug1) as H1. pose proof (holds_mem _ _ _ HF Hug2) as H2. zf H1. zf H2.
  repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H2.
  rewrite !uval_lit in H1, H2 by lia. pose proof (uval_range r vUg). destruct SZ as [S1 S2 S3 S4].
  rewrite uval_add_small in H1 by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia.
  pose proof (HK r HF ltac:(split; assumption)) as HKr.
  destruct (pay_K_arith (uval r vUg) (uval r vSZ) (uval r k - 32) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [A B].
  split; [lia|]. split; [lia | exact NN].
Qed.

Lemma X_X_K : ltac2:(tb__ "0|8|
S5Sc8SdSbS2cS48Q40A1A1M0S4G0Se8S9cVrho0;SadVCST;VFB;VFF;A3S12S6R7A1A1SeZ0M1A1G1S59S33S3dS2eS3dS3eZ1M2G1S2eS31S4S3fA2M3S32S4S3fG2S40R5A1A4S30G3A1M4A3G1A4S2eS3dS3eG1G2G4S26Z2M5S41A2A4S30S3dA1A3M6A3SdeS4dA1M7A3A8S0S2dS9R8S79R7A3S2fA3S0S2dScaR8S9cA2S2fA3S0S2dSf6S9cS17S6RaA1A1A2S2fA3S0S2dSa9S17S6RbA1A1Sa5S53S30S31S31SdS4A2SdA2A1S33S3dS2eS3dS3eG2G1S2eG3S32S4S3fG2S40R9A1A4G4A3G1A4G6A3G7A3S62A4A2S2fA3S0S2dS47S12S6RcA1A1S45RbS88A2S33S3dS2eS3dS3eG2G1S2eG3S32S4S3fG2S40RaA1A4G4A3G1A4G6A3G7A3A3S2fA3S0S2dSa6Sa7RcS62A2S62A2S2fA3S0S2dSf2RdS53S53A3S2fA3S23S26Z4cS25G5Z40A2A2RaA2VTR;S4aS29VJAv;S66A1R10RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fk;Fs;FX;").
Proof.
  intros X s k rho tp b tp0 HPAY He Hid Hnf Hnb Hle Ham Htv Hb.
  eapply TR_pre; [|apply (REENTER C_K ndKc (75, z0) (rho_sub rho s)); [innth 3 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X C_K s (NDA tv0 [] ([BI 1 0 [(1, ASv k)] 0; BI 0 1 [] (2 * KU)] ++ POT vSZ) am_np) ndKc);
    [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | exact Ham |].
  apply (JA_repay segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue tv0 [] bd_slow _ am_np X rho tp w HPAY Hw).
Qed.
Lemma X_X_K1 : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z4cS25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S66A1S7fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K1 s_K1 (SLit 65568));
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [repeat split; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros r HF SZ. left. factz HF (SPBranch BC_LTU (SAlu ALU_ADD vSZ (SLit 16)) (SLit 65536)) H1.
  destruct SZ. rewrite !uval_lit in * by lia. rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia. lia.
Qed.
Lemma X_X_K2 : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z4cS25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S66A1S80R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K2 s_K2 (SAlu ALU_ADD vSZ (SLit 48)));
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [repeat split; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros r HF SZ. right. factz HF (SPNot (SPBranch BC_LTU (SAlu ALU_ADD vSZ (SLit 16)) (SLit 65536))) H1.
  destruct SZ. rewrite !uval_lit in * by lia. rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia.
  rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma site_m : ltac2:(tb__ "0|1|
SbSe9VAInv;VCST;VXGL;S9cVrho0;SadVCST;VFB;VFF;A3VFB;VFF;S55S52S56R1S76S39S4A1Se4Sd1S1S1S23Z1S3cR3Sc9S52PcA2A2M0A2S27G0S25Z2Z27A2A2A2Sc5S30SbbA1SbaSc7Sc6R3S56R1A3S52A2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndKc] in HN, HD, HZ, HFR.
  assert (SZ : srcz rho) by srcz_tac HF. pose proof (srcP_of rho HP0 Hav) as SP.
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None is_src R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
    + intros o a Ho Hb Hr. unfold is_src in Hb.
      apply lazy_andb_prop in Hb as [H1 Hb]. apply lazy_andb_prop in Hb as [H2 H3].
      apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
      apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HT). apply SP. apply (src_range rho a SZ).
      destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi] in H1, H2, H3. subst.
      unfold obj_range, obj_lo_of, obj_hi_of, O_src in Hr |- *. cbn [ob_base ob_lo ob_hi fst snd] in Hr |- *. exact Hr.
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) is_srcX (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
    + intros r a Hr Hb Ha. unfold is_srcX in Hb. apply lazy_andb_prop in Hb as [H1 H2]. apply sv_eqb_sound in H1. apply sv_eqb_sound in H2.
      left. apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HT). apply SP. destruct r as [rb rl]. cbn [fst snd] in H1, H2, Ha. subst. exact Ha.
    + exact I.
  - change (wsub_get s_m 12) with (e32 vK). factz HF (SPUle (SLit 65536) vK) H1. factz HF (SPUle vK (SLit (2 ^ 32 + 16))) H2.
    rewrite !uval_lit in H1, H2 by lia. unfold e32. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma X_E_m : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z42S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S76A1S55R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (malloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp ndKc bd_m (FAM b tp0) CMALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull ndM (65, z0)); [innth 4 | meas].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok ndMok (65, z0)); [innth 5 | meas]].
    intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). vm_compute. reflexivity.
Qed.

Lemma used_new_val : ltac2:(tb__ "0|0|
SbS0S48Q40A1S19R1S4dA2S19R1S97A2A3Fr;").
Proof.
  intros r. reflexivity.
Qed.

Lemma X_X_sret : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z33S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S8eA1S72R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndL) C_loop rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_sret X_sret1 tp _ X_sret1_eq Hw) as H1.
    pose proof (AxCellA.SPA_recellv segs _ rho X_sret1 iH jU vSZ (fst rcU) (snd rcU) tp _ ltac:(rewrite rcU_eq; destruct rcU; reflexivity)
                  ltac:(vm_compute; reflexivity) (fun _ => used_new_val rho) H1) as H1r.
    rewrite X_sret1r_eq in H1r.
    pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m bd_m2 0 blkN vHD vK vSZ
                  X_sret1r objsN ohN otN rho tp tr ms md objsN_eq eq_refl) as H2.
    specialize (H2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) H1r).
    rewrite X_sret2_eq in H2. cbn [remove_nth fst blkN] in H2.
    set (rho1 := rho_absorb rho [otN] (vms md tp ms)) in H2.
    assert (HF1 : Forall (holds rho1) (ss_facts (ax_S X_sret2))) by exact (smatchA_facts segs _ _ _ _ (proj1 H2)).
    assert (SZ1 : srcz rho1) by srcz_tac HF1.
    factz HF1 (SPUle (SAlu ALU_ADD (SVar pN) (e32 vK)) (SVar 30)) HE1. factz HF1 (SPUle (SVar pN) (SVar 30)) HE2.
    factz HF1 (SPUle (SLit 65536) vK) HK1. factz HF1 (SPUle vK (SLit (2 ^ 32 + 16))) HK2. factz HF1 (SPUle (SAlu ALU_ADD vSZ (SLit 16)) vK) HK3.
    factz HF1 (SPUle (SVar 30) (SLit 140737479966720)) HT30. rewrite !uval_lit in HT30, HK1, HK2 by lia.
    pose proof (uval_range rho1 (SVar pN)) as RP. pose proof (uval_range rho1 vK) as RK.
    assert (EK : uval rho1 (e32 vK) = uval rho1 vK + 32) by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small in HE1 by (rewrite EK; lia). rewrite EK in HE1.
    rewrite uval_add_small in HK3 by (rewrite uval_lit by lia; destruct SZ1; lia). rewrite uval_lit in HK3 by lia.
    assert (EPn : uval rho1 p_new = uval rho1 (SVar pN) + 32) by (unfold p_new; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    assert (H3 : SPA segs (JAv (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD vK [(p_new, vSZ)]))) X_sret3 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_sret3_eq.
      apply (SPA_refacts_JA segs _ rho1 (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2))); [| vm_compute; reflexivity |].
      - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_m2 (SVar pN) vHD vK p_new vSZ X_sret2 rho1 tp _);
          [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact H2].
        + intros r HFr. assert (SZr : srcz r) by srcz_tac HFr.
          factz HFr (SPUle (SAlu ALU_ADD vSZ (SLit 16)) vK) HK3'. factz HFr (SPUle vK (SLit (2 ^ 32 + 16))) HK2'. rewrite uval_lit in HK2' by lia.
          rewrite uval_add_small in HK3' by (rewrite uval_lit by lia; destruct SZr; lia). rewrite uval_lit in HK3' by lia.
          pose proof (uval_range r (SVar pN)). unfold p_new.
          rewrite uval_add_small by (rewrite uval_lit by lia; factz HFr (SPUle (SVar pN) (SVar 30)) HE; factz HFr (SPUle (SVar 30) (SLit 140737479966720)) HT30'; rewrite uval_lit in HT30' by lia; lia).
          rewrite uval_lit by lia. destruct SZr. lia.
        + intros Ai rho2 tp2 md2 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho1 Hav eq_refl) as ET. split.
          * intros o a Ho Hr. rewrite objsN2_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
            -- destruct (objs_ok_ad rho1 objsN ltac:(basez_tac HF') SZ1 (srcP_of rho1 HP0 Hav)
                          ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 12)
                          ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
            -- right; right. unfold ohN in Hr. apply range_lit' in Hr; [|lia|lia]. unfold pN. lia.
          * intros r a Hr Ha.
            assert (HX : In r [(vAR, SLit 64); (vSRC, vLS); (SVar pN, e32 vK)]) by exact Hr. clear Hr.
            pose proof (AAP.basez_of rho1 _ HF' ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
            destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
            -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *. lia.
            -- destruct SZ1 as [_ _ [S1 S2] ST]. lia.
            -- rewrite EK in Ha. lia.
      - intros tr' md' _ HF2. apply Forall_app. split; [|exact HF2].
        unfold new_facts. destruct SZ1. change (bv_unsigned (rw rho1 V_TOP)) with (uval rho1 (SVar 30)) in *.
        assert (EPS : uval rho1 (SAlu ALU_ADD p_new vSZ) = uval rho1 p_new + uval rho1 vSZ) by (rewrite uval_add_small by lia; lia).
        assert (EHC : uval rho1 (SAlu ALU_ADD (SVar pN) (e32 vK)) = uval rho1 (SVar pN) + (uval rho1 vK + 32)) by (rewrite uval_add_small by (rewrite EK; lia); rewrite EK; lia).
        repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
          rewrite ?EPS, ?EHC, ?EPn; rewrite ?uval_lit by lia; lia. }
    exists (rho_sub rho1 s_sret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_sret3 C_loop s_sret (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD vK [(p_new, vSZ)])) ndL);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
  apply TR_exw. intros rho'. apply (REENTER C_loop ndL (50, SAlu ALU_SUB vSZ vI)); [innth 6 | meas].
Qed.

Lemma X_X_ret : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S8dA1S71R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndK) P_ok rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_ret X_ret1 tp _ X_ret1_eq Hw) as H1.
    pose proof (JA_unslot segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HNP tv0 [] bd_loop vH vNXl vCAPl vP vSZ
                  X_ret1 (objsR ++ [ohR]) osR rho tp tr ms md objsR_eq ltac:(vm_compute; reflexivity) H1) as H2.
    rewrite X_ret2_eq in H2. set (rho1 := rho_absorb rho [osR] (vms md tp ms)) in H2.
    pose proof (JA_close segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_loop [] vH vNXl vCAPl vUc
                  X_ret2 objsR ohR rho1 tp tr ms md objsR2_eq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; left; reflexivity) eq_refl ltac:(vm_compute; reflexivity) H2) as H3.
    rewrite X_ret3_eq in H3. set (rho2 := rho_absorb rho1 [ohR] (vms md tp ms)) in H3.
    exists (rho_sub rho2 s_ret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_ret3 P_ok s_ret (NDA tv0 [] [] (AHead vH true)) ndK);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
  apply TR_exw. intros rho'. apply X_P_ok.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S5S9dS31S4SdA2M0SbS2cS48Q40A1A1M1G1S9aS31S31S5S9dA2M2G0A2S32G2G0S32S5S9dR6R5A4R4A4S75A3VTR;S4aS29VJAv;R6A1R7R4R3A5VFAM;Sa2S32G2G0S32S5S9dR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_open. meas.
  - apply X_X_nohead. meas.
  - apply X_X_nofitO.
  - apply X_X_fit. meas.
  - apply X_X_nofit. meas.
  - apply X_X_K1. meas.
  - apply X_X_K2. meas.
  - apply X_E_m. meas.
  - apply X_X_sret. meas.
  - apply X_X_ret.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
SabS29VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sc2S29Sb9VAInv;VCST;VXGL;A5").

Theorem arena_dup_sum : ltac2:(tb__ "0|0|
S2cS48Q40A1A1Sb7S29Vok;S4aS29Sa1VAInv;VCST;VXGL;VKc;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eS5aAaS6dVrho0;R1A5Sb0S29S9cVrho0;R1Sd4A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc ALA FUEL_ad cutpcs_ad 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertA_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_false segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok))
         with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_ad CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_ad P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sc3S29Sb9VAInv;VCST;VXGL;A5").

Theorem arena_dup_sum_ex : ltac2:(tb__ "0|0|
S2cS48Q40A1A1Sb6S29S4aS29Sa1VAInv;VCST;VXGL;VKc;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eS5aAaS6dVrho0;R1A5Sb0S29S9cVrho0;R1Sd4A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc ALA FUEL_ad cutpcs_ad 100 cutsE exitsE (Q tp0) ejcertA_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_false segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_ad CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_ad P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_finalize_shape_dup2_pf.

(* [comment removed for export] *)
Module Lib_finalize_unknowns.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "pair"; "prod"; "None"; "bool"; "false"; "nat"; "true"; "app"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "cell"; "sprop"; "sobj"; "SPUle"; "FcsrFrm0"; "mkSS"; "valuation"; "DUnknown"; "SAlu"; "SPAlign"; "SVar"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vb"; "piece"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_unknowns"; "FUEL_fu"; "Pre_fu"; "cutpcs_fu"; "P_fu"; "Posts_fu"; "cuts_fu"; "fu_facts"; "fu_objs"; "NXP_fu"; "O_fstk"; "Vd"; "exits_fu"; "vcuts_fu"; "vexits_fu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_unknowns.FinUnkAddr"; "fu_entry"; "fu_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module FinUnkAddr.
  Definition fu_entry : Z := 0x917fc.
  Definition fu_ret : Z := 0x91cfc.
End FinUnkAddr.
Import FinUnkAddr.

Definition FUEL_fu : nat := 100%nat.
Definition NXP_fu : positive := 140%positive.

Definition O_fstk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S18PaA1ScNd0A1ScZ0A1Vcells;S15A5").

Definition Vd (o e : Z) : sobj := ltac2:(tb__ "0|1|
S23Vo;S2aVo;Z20A2S0SeS24Vo;ScZ0A1M0A2S0SeS24S2aVo;Z8A2G0A2S0SeS24S2aVo;Z10A2G0A2S0SeS24S2aVo;Z18A2ScVe;A1A2S1SeA1A3A3A3A3A3").
Definition fu_facts : list sprop := ltac2:(tb__ "0|0|
S0SfS17PcZ4A2S0SfS11ScS4aA1S22A2S0SfS11S16S42S22ScZ518A1A3ScZ7fffff800000A1A2S0SfS11S22ScS25A1A2S1SfA1A3A3A3A3").
Definition fu_objs : list sobj := ltac2:(tb__ "0|0|
SaS10S0S10S34S1SeA1A1S0S10S35Z1a0Z18A2S1S10A1A3A3S1cA3").

Definition Pre_fu : axst := ltac2:(tb__ "0|1|
S1bS13S43S20S1eS12S5SdA1S32S31S1dS7A9S0S4SdSdA2M0S3SdSdS22ScZ518A1A4S1G0A1A3A2").
Definition P_fu : axst := ltac2:(tb__ "0|2|
S1bS13S44S21S1fS1dA1S0S4S8SdA2M0S3S8SdUaScZ0A1A4S1G0A1A3A2S1eS12S5SdA1S32S31S33S7A9S0S4SdSdA2M1S3SdSdS22ScZ518A1A4S1G1A1A3A2").
Definition Posts_fu : list leafA := ltac2:(tb__ "0|0|
S0S39S3aS2eS48A2S1S39A1A3").

Definition cuts_fu : list axst := [Pre_fu].
Definition exits_fu : list axst := [P_fu].
Definition cutpcs_fu : list Z := [].

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Definition check_fu__runs : ltac2:(tb__ "0|0|
S2SbS2S39A1A1A1") := ltac2:(tb__ "0|0|
S49S1aS2bS2dS30A4").
Lemma check_fu : ltac2:(tb__ "0|0|
S3bS6S28S1aS2bS2dS1dS30S36A6S9A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUEL_fu cutpcs_fu NF cuts_fu exits_fu check_fu__runs); [unfold check_fu__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem finalize_unknowns_sum : ltac2:(tb__ "0|0|
S47OF_;S3eS14S2S41Q40A1A1S40S1aR4R3A3S3fS1aS1dR4A3S46S1aR6S3dS1aR5S2cR4R3A5S3cS1aR5S1dR4R3S2fA6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_fu rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_fu cutpcs_fu NF cuts_fu exits_fu (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_fu) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_fu.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply exit_postA. in_nth 0.
  - left; reflexivity.
Qed.

Definition vcuts_fu : list vnodeA := ltac2:(tb__ "0|0|
S0S26S27S2cZ1eScZ0A1A3S1S26A1A3").
Definition vexits_fu : list vnodeA := ltac2:(tb__ "0|0|
S0S26S27S2eZ1ScZ0A1A3S1S26A1A3").

Lemma echeck_fu : ltac2:(tb__ "0|0|
S3bS6S29S1aS2bS2dS1dS37S38A6S9A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUEL_fu cutpcs_fu NF vcuts_fu vexits_fu check_fu__runs); [unfold check_fu__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem finalize_unknowns_sum_ex : ltac2:(tb__ "0|0|
S3eS14S2S41Q40A1A1S3fS1aS1dR3A3S45S1aS3dS1aR4S2cR3R2A5S3cS1aR4S1dR3R2S2fA6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_fu rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_fu with (vna_state (mkVNA Pre_fu 30 (SLit 0))).
  apply (cfg_complete_autoA segs FUEL_fu cutpcs_fu NF vcuts_fu vexits_fu (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_fu) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. destruct Hin as [<-|[]]; cbv; congruence.
  - exact echeck_fu.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply (eexit_postA segs J NF rho vcuts_fu Posts_fu (mkVNA P_fu 1 (SLit 0))). in_nth 0.
  - left; reflexivity.
Qed.
End Lib_finalize_unknowns.

