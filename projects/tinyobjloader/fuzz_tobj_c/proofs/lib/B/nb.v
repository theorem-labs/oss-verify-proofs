(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7 na DrvFw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.

(* [comment removed for export] *)
Module Asan_memcpy.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "bool"; "true"; "prod"; "app"; "Some"; "list"; "option"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "cell"; "mkCell"; "sprop"; "sobj"; "mkObj"; "DUnknown"; "SAlu"; "sprop_below"; "ss_next"; "SPBranch"; "SPUle"; "FcsrFrm0"; "mkSS"; "DImage"; "SPNot"; "SPAlign"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "entailsA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "tv"; "dst"; "cur"; "gl"; "gs"; "src"; "F_L"; "vBd"; "vBs"; "vLd"; "vLs"; "F8of"; "lastd"; "lasts"; "X_mc"; "hi_fact"; "lo_fact"; "opnd_facts"; "xor_facts"; "O_dst"; "O_real"; "O_rtc3"; "O_src"; "ord1"; "ord2"; "vOd"; "vOs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GEU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "vN"; "add"; "shp"; "P_ret"; "shpk"; "O_rtc2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memcpy"; "mid_state"; "E_real"; "FT"; "E_dst"; "E_src"; "R_dst"; "R_src"; "s_dst"; "s_src"; "CLd_0"; "CLs_0"; "R_real"; "s_real"; "E_Ld_bk"; "E_Ld_in"; "E_Ls_bk"; "E_Ls_in"; "P_amc"; "ld_regs"; "ls_regs"; "objs_mc"; "spm"; "CLd"; "CLs"; "E_dst_hi"; "E_dst_lo"; "E_src_hi"; "E_src_lo"; "FUELM"; "Pre_mc0"; "Pre_mc1"; "Pre_mc2"; "T1"; "T2"; "T3a"; "T3b"; "base_mc"; "cutpcs_mc"; "s_Ld_bk"; "s_Ld_in"; "s_Ls_bk"; "s_Ls_in"; "O_cstk"; "O_frame"; "O_rest"; "T1r"; "T2r"; "T3ar"; "T3br"; "cuts_mc"; "exits_mc"; "frame_cells"; "mid_regs"; "vDp"; "vcuts_mc"; "vexits_mc"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "NPOST"; "post_regs"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "Pre_rip_lo"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memcpy.AMCAddr"; "ld_head"; "ls_head"; "musl_memcpy"; "mc_entry"; "mc_ret"; "ra_dst"; "ra_real"; "ra_src"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "Pre_memcpyA"; "liftA"; "memcpy_entryA"; "Posts_memcpyA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "segs"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy"; "P_retA"; "P_retB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import RegionAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module AMCAddr.
  Definition mc_entry : Z := 0x5c9e0.
  Definition mc_ret : Z := 0x5cb08.
  Definition ra_src : Z := 0x5cd84.
  Definition ra_dst : Z := 0x5ce24.
  Definition ra_real : Z := 0x5cadc.
  Definition ls_head : Z := 0x5cd54.
  Definition ld_head : Z := 0x5cdf8.
  Definition musl_memcpy : Z := 0xdac00.
End AMCAddr.
Import AMCAddr.

Definition frame_cells : list cell := ltac2:(tb__ "0|1|
S0S10S11SfN48A1Z8M0SeP2bA1A3S0S10S11SfN40A1G0SeP2aA1A3S0S10S11SfN38A1G0SeP29A1A3S0S10S11SfN30A1G0SeP28A1A3S0S10S11SfN28A1G0SeP27A1A3S0S10S11SfN20A1G0SeP26A1A3S0S10S11SfN18A1G0SeP1dA1A3S0S10S11SfN10A1G0SeP1cA1A3S0S10S11SfN8A1G0SePbA1A3S3S10A1A3A3A3A3A3A3A3A3A3").
Definition O_frame (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S14SePaA1SfN860A1SfZ0A1Vcs;S15A5").
Definition spm : sv := add (SVar 10) (SLit (-2144)).
Definition O_cstk : sobj := ltac2:(tb__ "0|0|
S14S67SfN50A1SfZ0A1S3S10A1S15A5").
Definition vDp : sv := SVar 95.
Definition O_rest : sobj := ltac2:(tb__ "0|0|
S14SePaA1S87SfN8b0A1S3S10A1S15A5").
Definition objs_mc (fr : list cell) : list sobj := ltac2:(tb__ "0|0|
S7S13S0S13S7dVfr;A1S0S13S7cS0S13S7eS0S13S3dS0S13S40S0S13S3fS0S13S51S0S13S3eS3S13A1A3A3A3A3A3A3A3A3SabA3").

Definition base_mc : list sprop := ltac2:(tb__ "0|3|
S7S12S3bS31S33S43PfA4S7S12S3bS32S34S44P13A4S0S12S1aSfZ1A1S4cA2S0S12S1aS4cSfS8aZ2M0Z28A2A1A2S0S12S1fPaM1Z4A2S0S12S1aSfS8bSaaZ900A2A1SeG1A1M2A2S0S12S1aG2SfS8aG0Z3fA2A1A2S3S12A1A3A3A3A3A3A3A3").
Definition FT : list sprop := xor_facts ++ base_mc.

Definition Pre_mc0 : axst := ltac2:(tb__ "0|1|
Sa8S1cS9dS8fS90S0S6S2SdA2M0S1S2SdUaS2bA4S0G0S1S2SdUbS2fA4S0G0S1S2SdUcS4cA4S3G0A1A3A3A3A2S8eS1bSbSdA1S66S3S10A1A1S76S8dScA9S38A2").
Definition Pre_mc1 : axst := ltac2:(tb__ "0|0|
S47S0S12S41S3cA3S6fA2").
Definition Pre_mc2 : axst := ltac2:(tb__ "0|0|
S47S0S12S42S3cA3S6fA2").

Definition P_amc : axst := ltac2:(tb__ "0|1|
Sa8S1cS9eS8fS92S8dA1S0S6S2SdA2M0S1S2SdUaS2bA4S3G0A1A3A2S8eS1bSbSdA1S66S3S10A1A1S76S91ScA9S38A2").
Definition Posts_mc : list leafA := ltac2:(tb__ "0|0|
S0S25S29S63SadA2S3S25A1A3").

Definition mid_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|17|
S8fS90S7S6S2SdA2M0S0G0S1S2SdU1M1S2aG1A1A4S0G0S1S2SdU2S67A4S0G0S1S2SdU5M2S2aG2A1A4S0G0S1S2SdU6M3S2aG3A1A4S0G0S1S2SdU7M4S2aG4A1A4S0G0S1S2SdU8SePaA1A4S0G0S1S2SdU9M5S2aG5A1A4S0G0S1S2SdUaM6S2aG6A1A4S0G0S1S2SdUbM7S2aG7A1A4S0G0S1S2SdUcM8S2aG8A1A4S0G0S1S2SdUdM9S2aG9A1A4S0G0S1S2SdUeMaS2aGaA1A4S0G0S1S2SdUfMbS2aGbA1A4S0G0S1S2SdU10McS2aGcA1A4S0G0S1S2SdU11MdS2aGdA1A4S0G0S1S2SdU12MeS2aGeA1A4S0G0S1S2SdU13MfS2aGfA1A4S0G0S1S2SdU14S67A4S0G0S1S2SdU15M10S2aG10A1A4S0G0S1S2SdU16M11S2aG11A1A4S0G0S1S2SdU17M12S2aG12A1A4S0G0S1S2SdU1cM13S2aG13A1A4S0G0S1S2SdU1dM14S2aG14A1A4S0G0S1S2SdU1eM15S2aG15A1A4S0G0S1S2SdU1fM16S2aG16A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition mid_state (pc : Z) (l : list (nat * sv)) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
Sa8S1cVpc;S86Vl;A1S8eS1bSbSdA1S66S85A1S7S12Vfacts;S54A3PbeScA9S38A2").

Definition E_src : axst := ltac2:(tb__ "0|1|
S52SacS0S6S2SdA2M0S1S2SdU1SfSa1A1A4S0G0S1S2SdUaS2fA4S0G0S1S2SdUbS4cA4S0G0S1S2SdU9S4cA4S0G0S1S2SdU13S4dS2bS4cA2A4S0G0S1S2SdU15S2bA4S0G0S1S2SdU16S4dS4cSfN41A1A2A4S0G0S1S2SdU17S2fA4S3G0A1A3A3A3A3A3A3A3A3S3S12A1A3").

Definition E_dst : axst := ltac2:(tb__ "0|1|
S52SacS0S6S2SdA2M0S1S2SdU1SfS9fA1A4S0G0S1S2SdUaS2bA4S0G0S1S2SdUbS4cA4S0G0S1S2SdU9S2bA4S0G0S1S2SdU15S2fA4S0G0S1S2SdU12S4cA4S3G0A1A3A3A3A3A3A3S3S12A1A3").

Definition E_src_hi : axst := ltac2:(tb__ "0|0|
S47S0S12S39S32A1S3S12A1A3S56A2").
Definition E_src_lo : axst := ltac2:(tb__ "0|0|
S47S0S12S3aS32S34A2S3S12A1A3S56A2").
Definition E_dst_hi : axst := ltac2:(tb__ "0|0|
S47S0S12S39S31A1S3S12A1A3S55A2").
Definition E_dst_lo : axst := ltac2:(tb__ "0|0|
S47S0S12S3aS31S33A2S3S12A1A3S55A2").

Definition E_real : axst := ltac2:(tb__ "0|1|
S52S9cS0S6S2SdA2M0S1S2SdU1SfSa0A1A4S0G0S1S2SdUaS2bA4S0G0S1S2SdUbS2fA4S0G0S1S2SdUcS4cA4S3G0A1A3A3A3A3S3S12A1A3").

Definition ls_regs (a3 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S2SdA2M0S1S2SdUaS2bA4S0G0S1S2SdUbS2fA4S0G0S1S2SdUcS4cA4S0G0S1S2SdUdVa3;A4S0G0S1S2SdUeS4eS2dA1A4S0G0S1S2SdU13S4dS2bS4cA2A4S0G0S1S2SdU16S4dS4cSfN41A1A2A4S3G0A1A3A3A3A3A3A3A3").
Definition CLs_0 : axst := ltac2:(tb__ "0|0|
S52S9bS65S4eS2cA1A1S3S12A1A3").
Definition CLs : axst := ltac2:(tb__ "0|0|
S47S30S32S34S37A3S5cA2").
Definition E_Ls_in : axst := ltac2:(tb__ "0|1|
S52S9bS65S4eS2eA1M0A1S7S12S35S2eP8eS2fA3S7S12S35S2dP8dS37A3S0S12S1eS19S4aG0S4eS2dA1A3A1S3S12A1A3A3A3A3").
Definition E_Ls_bk : axst := ltac2:(tb__ "0|1|
S52S9bS65S50S2cZ1A2M0A1S7S12S30S32S34S37A3S0S12S19S4bG0S4eS2dA1A3S3S12A1A3A3A3").

Definition ld_regs (a3 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S2SdA2M0S1S2SdUaS2bA4S0G0S1S2SdUbS2fA4S0G0S1S2SdUcS4cA4S0G0S1S2SdUdVa3;A4S0G0S1S2SdUeS4eS2dA1A4S3G0A1A3A3A3A3A3").
Definition CLd_0 : axst := ltac2:(tb__ "0|0|
S52S9aS64S4eS2cA1A1S3S12A1A3").
Definition CLd : axst := ltac2:(tb__ "0|0|
S47S30S31S33S36A3S5bA2").
Definition E_Ld_in : axst := ltac2:(tb__ "0|1|
S52S9aS64S4eS2eA1M0A1S7S12S35S2eP8eS2bA3S7S12S35S2dP8dS36A3S0S12S1eS19S4aG0S4eS2dA1A3A1S3S12A1A3A3A3A3").
Definition E_Ld_bk : axst := ltac2:(tb__ "0|1|
S52S9aS64S50S2cZ1A2M0A1S7S12S30S31S33S36A3S0S12S19S4bG0S4eS2dA1A3S3S12A1A3A3A3").

Definition s_src : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLs) :: infer_sub 1 (ax_S E_src) (ax_S Pre_rip)) in exact x).
Definition s_dst : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLd) :: infer_sub 1 (ax_S E_dst) (ax_S Pre_rip)) in exact x).
Definition s_real : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 (ax_S E_real) (ax_S Pre_memcpyA)) in exact x).
Definition R_src : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_src_hi Pre_rip s_src with Some R => R | None => [] end) in exact x).
Definition R_dst : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_dst_hi Pre_rip s_dst with Some R => R | None => [] end) in exact x).
Definition R_real : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_real Pre_memcpyA s_real with Some R => R | None => [] end) in exact x).

Lemma fr_src_hi : ltac2:(tb__ "0|1|
S22SaS9S13A1M0A1S98S6cS94S5aA3S8G0S58A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_src_lo : ltac2:(tb__ "0|1|
S22SaS9S13A1M0A1S98S6dS95S5aA3S8G0S58A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_dst_hi : ltac2:(tb__ "0|1|
S22SaS9S13A1M0A1S98S6aS94S59A3S8G0S57A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_dst_lo : ltac2:(tb__ "0|1|
S22SaS9S13A1M0A1S98S6bS95S59A3S8G0S57A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_real : ltac2:(tb__ "0|1|
S22SaS9S13A1M0A1S98S53Sa3S5eA3S8G0S5dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_src_hi : ltac2:(tb__ "0|0|
S22S4S97S6cS94S5aS58S96S25S24S27Sa2A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_src_lo : ltac2:(tb__ "0|0|
S22S4S97S6dS95S5aS58S96S25S24S27Sa2A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_dst_hi : ltac2:(tb__ "0|0|
S22S4S97S6aS94S59S57S96S25S24S27Sa2A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_dst_lo : ltac2:(tb__ "0|0|
S22S4S97S6bS95S59S57S96S25S24S27Sa2A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_real : ltac2:(tb__ "0|0|
S22S4S97S53Sa3S5eS5dS96S25S24S27Sa6A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T1r : axst := ltac2:(tb__ "0|0|
S99S5aS94S4fS56S58A5").
Definition T2r : axst := ltac2:(tb__ "0|0|
S99S59S94S4fS55S57A5").
Definition T3ar : axst := ltac2:(tb__ "0|0|
S99S5eSa3Sa4SaeSa5A1A1S53S5dA5").
Definition T3br : axst := ltac2:(tb__ "0|0|
S99S5eSa3Sa4SafSa5A1A1S53S5dA5").
Definition T1 : axst := ax_add_facts FT T1r.
Definition T2 : axst := ax_add_facts FT T2r.
Definition T3a : axst := ax_add_facts FT T3ar.
Definition T3b : axst := ax_add_facts FT T3br.

Definition cuts_mc : list axst := ltac2:(tb__ "0|0|
S0S24S70S0S24S71S0S24S72S0S24S73S0S24S74S0S24S75S0S24S69S0S24S68S3S24A1A3A3A3A3A3A3A3A3").
Definition exits_mc : list axst := ltac2:(tb__ "0|0|
S0S24S63S0S24S56S0S24S55S0S24S53S0S24S62S0S24S61S0S24S60S0S24S5fS3S24A1A3A3A3A3A3A3A3A3").
Definition cutpcs_mc : list Z := ltac2:(tb__ "0|0|
S0S21SacS0S21S9cS0S21S9bS0S21S9aS3S21A1A3A3A3A3").
Definition FUELM : nat := 800%nat.

Definition vcuts_mc : list vnodeA := ltac2:(tb__ "0|6|
S0S45S46S70Zc8M0SfZ0A1M1A3S0S45S46S71G0G1A3S0S45S46S72Z77SfS8aZ2M2Z3dA2A1A3S0S45S46S73Z4fSfS8aG2Z3fA2M3A1A3S0S45S46S74Z27M4SfS8bG3Z8A2A1M5A3S0S45S46S75G4G5A3S0S45S46S69Z96S2cA3S0S45S46S68Z64S4dS2cSfS8aG2Z3eA2A1A2A3S3S45A1A3A3A3A3A3A3A3A3").
Definition vexits_mc : list vnodeA := ltac2:(tb__ "0|6|
S0S45S46S63Z0SfS8cS8aZ2M0Z40A2Z1M1A2A1A3S0S45S46S56Z78SfS8aG0Z3dA2A1A3S0S45S46S55Z50SfS8aG0Z3fA2M2A1A3S0S45S46S53Z28SfS8bG2Z8A2A1A3S0S45S46S62Z97M3S2eA3S0S45S46S61G3S4dS2cSfG1A1A2A3S0S45S46S60Z65M4S4dS2eSfS8aG0Z3eA2M5A1A2A3S0S45S46S5fG4S4dS2cSfS8bG5G1A2A1A2A3S3S45A1A3A3A3A3A3A3A3A3").

Lemma echeck_mc : ltac2:(tb__ "0|0|
S22S4Sb0Sa9S6eS77S8dS88S89A6S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_mc : ltac2:(tb__ "0|0|
S22S4S48Sa9S6eS77S8dS83S84A6S5A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc cuts_mc exits_mc eq_refl eq_refl echeck_mc). Qed.

Definition s_Ls_in : wsub := ltac2:(tb__ "0|1|
S0S6S20SdA2M0S1S20SdP8cS2eA4S3G0A1A3").
Definition s_Ls_bk : wsub := ltac2:(tb__ "0|1|
S0S6S20SdA2M0S1S20SdP8cS4dS2cSfZ1A1A2A4S3G0A1A3").
Definition s_Ld_in : wsub := ltac2:(tb__ "0|1|
S0S6S20SdA2M0S1S20SdP8cS2eA4S3G0A1A3").
Definition s_Ld_bk : wsub := ltac2:(tb__ "0|1|
S0S6S20SdA2M0S1S20SdP8cS4dS2cSfZ1A1A2A4S3G0A1A3").
Lemma ent_Ls_in : ltac2:(tb__ "0|0|
S22S4S28S62S5cS7bA3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ls_bk : ltac2:(tb__ "0|0|
S22S4S28S61S5cS7aA3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ld_in : ltac2:(tb__ "0|0|
S22S4S28S60S5bS79A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ld_bk : ltac2:(tb__ "0|0|
S22S4S28S5fS5bS78A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_mc : ltac2:(tb__ "0|0|
S23S22S4Sa7S7bS8dA2S5A3S23S22S4Sa7S7aS8dA2S5A3S23S22S4Sa7S79S8dA2S5A3S22S4Sa7S78S8dA2S5A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma FLs_below : ltac2:(tb__ "0|0|
S22S4S93S12S17S18S26S5cA1A1A1S30S32S34S37A3A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FLd_below : ltac2:(tb__ "0|0|
S22S4S93S12S17S18S26S5bA1A1A1S30S31S33S36A3A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma FT_below_E : ltac2:(tb__ "0|0|
S22S4S93S12S17P64A1S54A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FT_below_T : ltac2:(tb__ "0|0|
S23S22S4S93S12S17S18S26S7fA1A1A1S54A3S5A3S23S22S4S93S12S17S18S26S80A1A1A1S54A3S5A3S23S22S4S93S12S17S18S26S81A1A1A1S54A3S5A3S22S4S93S12S17S18S26S82A1A1A1S54A3S5A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Asan_memcpy.

(* [comment removed for export] *)
Module Icpt_memcpy_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "rw"; "holds"; "eval"; "ss_next"; "ss_facts"; "SVar"; "sprop_below"; "SLit"; "agree_below"; "SPBranch"; "SPNot"; "SAlu"; "sobj"; "soff"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "SHB"; "ACEIL"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "True"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "mul"; "sub"; "modulo"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_get"; "wsub_id_below"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "FT"; "Posts_mc"; "Pre_mc0"; "cur"; "F_L"; "E_src"; "E_dst"; "base_mc"; "gs"; "xor_facts"; "E_real"; "Pre_mc1"; "Pre_mc2"; "gl"; "E_Ld_bk"; "F8of"; "lastd"; "lasts"; "ord1"; "ord2"; "s_Ld_bk"; "s_Ld_in"; "s_Ls_bk"; "s_Ls_in"; "vBd"; "vBs"; "vLd"; "vLs"; "E_Ld_in"; "E_Ls_bk"; "E_Ls_in"; "R_dst"; "R_real"; "R_src"; "cuts_mc"; "hi_fact"; "lo_fact"; "opnd_facts"; "s_dst"; "s_real"; "s_src"; "vcuts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof"; "opZ"; "clsZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "add"; "shp"; "HSE"; "vN"; "g8"; "shpk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "ax_add_facts"; "withGA"; "vna_state"; "SPfamA"; "SPfamEA"; "enodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "call_checkA"; "entails_frA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof.OpZ"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "vmeasIA"; "to_enodeIA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_XOR"; "BC_GEU"; "BC_LTU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "Posts_memcpyA"; "Pre_memcpyA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr MCAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Section CallExit.
Variable ok : assn.
Variable J : jpredA.
Variable n : positive.
Variable rho0 : valuation.
Variable tp : list word.
Let J' : jpredA := ltac2:(tb__ "0|0|
S79S1SaVn;Vrho0;R1A3Lr;VJ;A2").

Variables (E Pre : axst) (s : wsub) (R : list sobj) (Posts : list leafA) (F : list sprop).
Hypothesis Hst : ltac2:(tb__ "0|0|
S36S11Vn;VJ;A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S17S2eS27SeA1M0A1S80VE;VPre;Vs;A3S2dG0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S17S28S7fVE;VPre;Vs;VR;S24S30S31S32VPosts;A4A5S29A3").
Hypothesis Hn : ltac2:(tb__ "0|0|
S81Vn;S5S2fVE;A1A1A2").
Hypothesis HF : ltac2:(tb__ "0|0|
S1S23S0S3R1A1S6S2fVE;A1A1A3S23S0S3R2A1VF;A3F_;Fr;").
Hypothesis HFb : ltac2:(tb__ "0|0|
S17S28S40S0S8S5S2fVE;A1A1A1VF;A3S29A3").
Hypothesis HFbT : ltac2:(tb__ "0|0|
S30S3fS30R1VPosts;A3S17S28S40S0S8S5S2fS7eVs;VPre;S32R2A1VE;VR;A5A1A1A1VF;A3S29A3F_;FL;").

Let Jp (rhoE : valuation) : jpredA := ltac2:(tb__ "0|1|
S1S27S15Q40A1A1M0S27S3aA1S39S16S17G0R3Vtp;A3VJ';VrhoE;R3R2R1A4A2Lmd;Ltr;Lt;L_;").
Let Jc : jpredA := ltac2:(tb__ "0|1|
S1S27S15Q40A1A1M0S27S3aA1S39S16S17G0R3Vtp;A3VJ';R4R3R2R1A4A2Lmd;Ltr;Lt;Lr;").

Lemma HstG : ltac2:(tb__ "0|0|
S36S11Vn;VJ';A3").
Proof. apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. Qed.

Lemma stable_Jp : ltac2:(tb__ "0|0|
S1S36S11S5S2fVPre;A1A1VJp;R1A1A3FrhoE;").
Proof.
  intros rhoE r r' t tr md md' Hag Hme [-> HJ]. split; [reflexivity|].
  eapply HstG; [apply agree_below_refl | exact Hme | exact HJ].
Qed.

Lemma okframe_Jp : ltac2:(tb__ "0|0|
S1S37S11Vok;VJ;A3S37S11Vok;VJp;R2A1A3F_;FrhoE;").
Proof.
  intros rhoE Hok r t tr ms md msv' [-> [_ HJ]]. eapply Hok; eauto.
Qed.

Lemma facts_transport : ltac2:(tb__ "0|1|
S1S1S23S0S3R2A1S6S2fVE;A1M0A1A3SaS5G0A1R3R2A3S23S0S3R3A1VF;A3F_;F_;Frho';FrhoE;").
Proof.
  intros rhoE rho' HFE Hag. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree (ss_next (ax_S E)) rhoE rho' p Hag (proj1 (forallb_forall _ _) HFb p Hp))).
  exact (proj1 (Forall_forall _ _) (HF rhoE HFE) p Hp).
Qed.

Lemma call_exitA : ltac2:(tb__ "0|1|
S27S31A1S76S37S11Vok;VJ;A3S74OF_;S35S1S27S15Q40A1A1S37S11R4R3A3S36S11S5S2fVPre;A1A1M0R4A3S75S11R6S33S11R5VPre;R4R3A5S34S11R5G0R4R3VPosts;A6A4F_;F_;Ftp1;Frho1;FJq;Fok';S30S3fS30R1VPosts;A3S3fS31S78VF;S7eVs;VPre;S32R2A1VE;VR;A5A2R6A3F_;FL;S1S75S11Vok;S33S11VJ';VE;R1Vtp;A5S74S18S7bS11VJ';R7Vtp;R1A5R6R1A1A2Lw;A4FrhoE;F_;F_;F_;FQ;Fcuts;").
Proof.
  intros cuts Q Hok Hsum Hcuts rhoE.
  apply triple_factsA. intros HFE.
  apply (call_soundA segs ok J' (Jp rhoE) (Jp rhoE) Jc E Pre s R Posts _ rhoE tp Hfr Hcc).
  - intros rho1 tp1. exact (Hsum ok (Jp rhoE) rho1 tp1 (okframe_Jp rhoE Hok) (stable_Jp rhoE)).
  - intros tr ms md Hsm HJ. split; [reflexivity | exact HJ].
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [-> HJ2]. split; [reflexivity|].
    eapply HstG; [ | apply mat_equiv_refl | exact HJ2].
    eapply agree_below_le; [exact Hn | exact (proj1 HLK)].
  - intros L rho' tpL HinL Hag.
    eapply triple_conseq; [ | intros w Hw; exact Hw | apply triple_refl].
    intros w [Hsm [-> HJ2]]. left. exists (ax_add_facts F (import_postA s Pre (la_state L) E R)), rho'.
    split; [exact (Hcuts L HinL)|]. split; [|exact HJ2].
    apply smatchA_add_facts; [exact Hsm | exact (facts_transport rhoE rho' HFE Hag) | exact (HFbT L HinL)].
Qed.

Lemma call_exitA_ex : ltac2:(tb__ "0|3|
S27S77A1S74OF_;S77S17S31S7aR1A1M0VE;A3S35S1S27S15Q40A1A1S36S11S5S2fVPre;A1A1M1R3A3S73S11S33S11R4VPre;R3R2A5S34S11R4G1R3R2VPosts;A6A3F_;Ftp1;Frho1;FJq;S30S3fS30R1VPosts;A3S19S77S77S16S3fS77R1R8A3S16S17S31G0S78VF;S7eVs;VPre;S32R3A1VE;VR;A5A2A3S1S1S16S1cZ0S84R3R1A2M2A2S1fG2S84R8R2A2A2A2Fr';Fr;A2A2LnT;A2F_;FL;S1S73S11S33S11VJ';VE;R1Vtp;A5S74S18S7cS11S24S77S7dS85VJ';A1R8A4Vtp;S84R6R2A2R1A5R7R1A1A2Lw;A3FrhoE;F_;F_;F_;FnE;FQ;Fvcuts;").
Proof.
  intros vcuts Q nE HnE Hsum Hcuts rhoE.
  apply etriple_factsA. intros HFE.
  apply (call_completeA segs J' (Jp rhoE) (Jp rhoE) Jc E Pre s R Posts _ rhoE tp Hfr Hcc).
  - intros rho1 tp1. exact (Hsum (Jp rhoE) rho1 tp1 (stable_Jp rhoE)).
  - intros tr ms md Hsm HJ. split; [reflexivity | exact HJ].
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [-> HJ2]. split; [reflexivity|].
    eapply HstG; [ | apply mat_equiv_refl | exact HJ2].
    eapply agree_below_le; [exact Hn | exact (proj1 HLK)].
  - intros L rho' tpL HinL Hag w [Hsm [-> HJ2]]. exists w. split; [apply wsteps_refl|]. left.
    destruct (Hcuts L HinL) as (nT & HinT & HT & Hm).
    exists (to_enodeIA J' nT), rho'. split; [apply in_map; exact HinT|].
    cbn [to_enodeIA ena_state ena_pred ena_meas fst snd]. rewrite HT. split; [| exact (Hm rhoE rho')].
    split; [|exact HJ2].
    apply smatchA_add_facts; [exact Hsm | exact (facts_transport rhoE rho' HFE Hag) | exact (HFbT L HinL)].
Qed.
End CallExit.

Section OpZ.
Variable rho : valuation.

Definition opZ (ib il io : positive) : Prop := ltac2:(tb__ "0|3|
S14Q40M0S2Vrho;Vib;A2A2S25S14G0S2Vrho;Vil;A2A2S25S14G0S2Vrho;Vio;A2A2S25S14G0S2Vrho;P12A2A2S25S16S1cS1dR2R1A2R3A2S16S1cR3S1eZ2M1Z28A2A2S16S1cZ1000R4A2S16S1cS1dR4R3A2S21S1eG1Z2fA2Z8M2A2A2S17S25S22R4G2A2Z0A3A2A2A2A2TN;TO;TL;TB;").

Lemma opnd_Z : ltac2:(tb__ "0|0|
S26S26S26S23S0S3Vrho;A1S66S7R3A1S7R2A1S7R1A1R3A4A3S83R4R3R2A3F_;Fio;Fil;Fib;").
Proof.
  intros ib il io HF.
  pose proof (urange (rw rho ib)) as RB. pose proof (urange (rw rho il)) as RL. pose proof (urange (rw rho io)) as RO.
  pose proof (urange (rw rho 18)) as RN.
  have_fact A1 HF (SPUle (add (SVar io) vN) (SVar il)). have_fact A2 HF (SPUle (SVar il) (SLit (2 ^ 40))).
  have_fact A3 HF (SPUle (SLit 4096) (SVar ib)). have_fact A4 HF (SPUle (add (SVar ib) (SVar il)) (SLit (2 ^ 47 - 8))).
  have_fact A5 HF (SPAlign ib 3). have_fact A6 HF (SPUle (SVar io) (SVar il)). have_fact A7 HF (SPUle vN (SVar il)).
  have_fact A8 HF (SPUle (SVar ib) (SLit (2 ^ 47 - 8))).
  unfold vN, add in A1, A2, A3, A4, A6, A7, A8.
  rewrite (U_lit64 rho (2 ^ 40)) in A2 by lia. rewrite (U_lit64 rho 4096) in A3 by lia.
  pose proof (U_lit64 rho (2 ^ 47 - 8) ltac:(lia)) as T47. rewrite T47 in A4. rewrite T47 in A8.
  cbn [eval] in A2, A3, A6, A7, A8.
  assert (B1 : 0 <= bv_unsigned (rw rho io) + bv_unsigned (rw rho 18) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar io) (SVar 18) (bv_unsigned (rw rho io)) (bv_unsigned (rw rho 18)) eq_refl eq_refl B1) in A1.
  cbn [eval] in A1.
  assert (B2 : 0 <= bv_unsigned (rw rho ib) + bv_unsigned (rw rho il) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar ib) (SVar il) (bv_unsigned (rw rho ib)) (bv_unsigned (rw rho il)) eq_refl eq_refl B2) in A4.
  destruct A5 as [_ A5]. change (2 ^ 3) with 8 in A5.
  unfold opZ. repeat split; lia.
Qed.

Lemma base_mc_Z : ltac2:(tb__ "0|4|
S23S0S3Vrho;A1S48A3S16S83PfP10P11A3S16S83P13P34P35A3S16S16S1cZ1S14Q40M0S2Vrho;P12A2A2M1A2S1cG1S1eZ2M2Z28A2A2A2S16S16S1cS1dS13Z1000A2S14G0S2Vrho;PaA2A2M3A2S1cG3S1eG2Z3fA2A2A2S17S25S22G3Z10A2Z0A3A2A2A2A2F_;").
Proof.
  intros HF. unfold base_mc in HF. apply Forall_app in HF as [HD HF]. apply Forall_app in HF as [HS HN].
  pose proof (urange (rw rho 18)) as RN. pose proof (urange (rw rho 10)) as R10.
  have_fact N1 HN (SPUle (SLit 1) vN). have_fact N2 HN (SPUle vN (SLit (2 ^ 40))).
  have_fact N3 HN (SPUle (SLit (ACEIL + 4096)) (SVar 10)). have_fact N4 HN (SPUle (SVar 10) (SLit (2 ^ 63))).
  have_fact N5 HN (SPAlign 10 4).
  unfold vN in N1, N2. rewrite (U_lit64 rho 1) in N1 by lia. rewrite (U_lit64 rho (2 ^ 40)) in N2 by lia.
  rewrite (U_lit64 rho (ACEIL + 4096)) in N3 by (unfold ACEIL; lia). rewrite (U_lit64 rho (2 ^ 63)) in N4 by lia.
  cbn [eval] in N1, N2, N3, N4. destruct N5 as [_ N5]. change (2 ^ 4) with 16 in N5.
  split; [exact (opnd_Z 15 16 17 HD)|]. split; [exact (opnd_Z 19 52 53 HS)|]. repeat split; lia.
Qed.
End OpZ.

Lemma rw_sub : ltac2:(tb__ "0|0|
S1S3cS26S17S15Q40A1S2S3bR3R2A2R1A2S4R3S3dR2R1A2A2A3Fi;Fs;Frho;").
Proof. reflexivity. Qed.

Section LoopZ.
Variables (ib il io : positive).
Let vB := SVar ib. Let vL := SVar il. Let vO := SVar io.
Let opd : sv := add vB vO.
Let lastx : sv := ltac2:(tb__ "0|0|
S6dS6dVopd;S70A2S9N1A1A2").
Hypothesis Hib : (ib < NF)%positive. Hypothesis Hil : (il < NF)%positive. Hypothesis Hio : (io < NF)%positive.

Section Vals.
Variable r : valuation.
Let B : ltac2:(tb__ "0|0|
S25") := ltac2:(tb__ "0|0|
S14Q40S2Vr;Vib;A2A2"). Let L : ltac2:(tb__ "0|0|
S25") := ltac2:(tb__ "0|0|
S14Q40S2Vr;Vil;A2A2"). Let O : ltac2:(tb__ "0|0|
S25") := ltac2:(tb__ "0|0|
S14Q40S2Vr;Vio;A2A2"). Let N := bv_unsigned (rw r 18).
Hypothesis HZ : ltac2:(tb__ "0|0|
S6bVr;Vib;Vil;Vio;A4").
Hypothesis HN : 1 <= N <= 2 ^ 40.

Lemma V_opd : ltac2:(tb__ "0|0|
S17S25S14Q40S4Vr;Vopd;A2A2S1dVB;VO;A2A3").
Proof using HZ HN.
  unfold opZ in HZ. pose proof (urange (rw r ib)). pose proof (urange (rw r io)). pose proof (urange (rw r il)).
  subst opd vB vO. unfold add. apply U_add2; [reflexivity | reflexivity | subst B L O N; unfold HSE in HZ; lia].
Qed.
Lemma V_last : ltac2:(tb__ "0|0|
S17S25S14Q40S4Vr;Vlastx;A2A2S21S1dS1dVB;VO;A2VN;A2Z1A2A3").
Proof using HZ HN.
  pose proof V_opd as Vo. unfold opZ in HZ. pose proof (urange (rw r ib)). pose proof (urange (rw r io)). pose proof (urange (rw r il)).
  subst lastx. unfold add at 1. unfold add at 1.
  replace (B + O + N - 1) with ((B + O + N) + (-1)) by lia.
  apply (U_addc r (SAlu ALU_ADD opd vN) (-1) (B + O + N)); [ | subst B L O N; unfold HSE in HZ; lia | lia].
  apply U_add2; [exact Vo | reflexivity | subst B L O N; unfold HSE in HZ; lia].
Qed.
Lemma V_BL : ltac2:(tb__ "0|0|
S17S25S14Q40S4Vr;S6dVvB;VvL;A2A2A2S1dVB;VL;A2A3").
Proof using HZ HN.
  unfold opZ in HZ. pose proof (urange (rw r ib)). pose proof (urange (rw r il)).
  subst vB vL. unfold add. apply U_add2; [reflexivity | reflexivity | subst B L O N; lia].
Qed.
Lemma V_g8 : ltac2:(tb__ "0|1|
S26S1fS14Q40M0S2Vr;R1A2A2S1eZ2Z3dA2A2S17S25S14G0S4Vr;S71S7R2A1A1A2A2S20Z8S14G0S2Vr;R2A2A2A2A3F_;Fv;").
Proof. intros v Hv. apply U_g8. exact Hv. Qed.
Lemma V_shp : ltac2:(tb__ "0|1|
S26S1fS14Q40M0S2Vr;R1A2A2S1eZ2Z3eA2A2S17S25S14G0S4Vr;S6eS7R2A1A1A2A2S1dS14G0S2Vr;R2A2A2S12A2A3F_;Fv;").
Proof. intros v Hv. apply U_shp. exact Hv. Qed.

Lemma F_L_intro : ltac2:(tb__ "0|3|
S25S25S17S25S14Q40M0S2Vr;P8cA2A2R2A3S17S25S14G0S2Vr;P8dA2A2R2A3S1cVB;S20Z8M1R4A2A2S1cS1dS20G1R5A2G1A2S1dVB;VL;A2A2S1fR6R5A2S1fR6S1eZ2Z3dA2A2S1cS20G1R7A2S21S1dS1dVB;VO;A2VN;A2Z1A2M2A2S1cG2S1dS20G1R8A2Z7A2A2S23S0S3Vr;A1S45VvB;VvL;Vlastx;A3A3F_;F_;F_;F_;F_;F_;F_;F_;Fl;Fc;").
Proof using HZ HN.
  intros c l Ec El H1 H2 H3 H4 H5 H6. unfold opZ in HZ.
  pose proof (urange (rw r ib)). pose proof (urange (rw r il)). pose proof (urange (rw r io)).
  assert (Hc : bv_unsigned (rw r 140) < 2 ^ 61) by lia.
  assert (Eg8c : UU r (g8 cur) = 8 * c) by (unfold cur; rewrite (V_g8 140 Hc); lia).
  assert (Eg8l : UU r (g8 gl) = 8 * l) by (unfold gl; rewrite (V_g8 141 ltac:(lia)); lia).
  unfold F_L, F8of.
  constructor. { cbn [holds]. rewrite Eg8c. change (eval r vB) with (rw r ib). lia. }
  constructor. { cbn [holds]. unfold add at 1. rewrite (U_addc r (g8 cur) 8 (8 * c) Eg8c) by lia. fold (add vB vL). rewrite V_BL. lia. }
  constructor. { cbn [holds]. reflexivity. }
  constructor. { cbn [holds]. rewrite (U_lit64 r (2 ^ 61 - 1)) by lia. change (eval r cur) with (rw r 140). lia. }
  constructor. { cbn [holds]. change (eval r cur) with (rw r 140). change (eval r gl) with (rw r 141). lia. }
  constructor. { cbn [holds]. rewrite Eg8l, V_last. lia. }
  constructor. { cbn [holds]. unfold add at 1. rewrite (U_addc r (g8 gl) 7 (8 * l) Eg8l) by lia. rewrite V_last. lia. }
  constructor. { cbn [holds]. rewrite (U_lit64 r (2 ^ 61 - 1)) by lia. change (eval r gl) with (rw r 141). lia. }
  constructor.
Qed.
End Vals.

Lemma in_facts_Z : ltac2:(tb__ "0|e|
S1S6bR1Vib;Vil;Vio;A4S16S1cZ1M0S14Q40M1S2R2P12M2A2A2M3A2S1cG3S1eZ2M4Z28A2A2A2S23S0S3R3A1S2cS0S50S49P8eM5Vopd;A3S2cS0S50S4eP8dM6Vlastx;A3S2aS0ScSbS89S6eS49A1S6eS4eA1A3A1S2bS0A1A3A3A3A3S14G1S2R4Vib;A2A2S25S14G1S2R5Vio;A2A2S25S14G1S2R6G2A2A2S25S14G1S2R7G5A2A2S25S14G1S2R8G6A2A2S25S16S16S1cS20Z8M7R2A2M8S1dR5R4A2M9A2S1cG9S1dG8Z7MaA2A2A2S16S1fR2S1eG4Z3dA2MbA2S16S16S1cS20G7R1A2McS21S1dG9R3A2G0A2MdA2S1cGdS1dGcGaA2A2A2S16S1fR1GbA2S1fR2R1A2A2A2A2A2Tl;Tg;TN;TO;TB;F_;F_;F_;Frho;").
Proof.
  intros rho HZ HN HF. pose proof HZ as HZ'. unfold opZ in HZ'.
  pose proof (urange (rw rho ib)). pose proof (urange (rw rho io)). pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  have_fact A1 HF (SPUle (g8 gs) opd). have_fact A2 HF (SPUle opd (add (g8 gs) (SLit 7))). have_fact A3 HF (SPUle gs (SLit (2 ^ 61 - 1))).
  have_fact A4 HF (SPUle (g8 gl) lastx). have_fact A5 HF (SPUle lastx (add (g8 gl) (SLit 7))). have_fact A6 HF (SPUle gl (SLit (2 ^ 61 - 1))).
  have_fact A7 HF (SPNot (SPBranch BC_GEU (shp gs) (shp gl))).
  rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia. rewrite (U_lit64 rho (2 ^ 61 - 1)) in A6 by lia.
  change (eval rho gs) with (rw rho 142) in A3. change (eval rho gl) with (rw rho 141) in A6.
  assert (Hg : bv_unsigned (rw rho 142) < 2 ^ 61) by lia. assert (Hl : bv_unsigned (rw rho 141) < 2 ^ 61) by lia.
  pose proof (V_g8 rho 142 Hg) as Eg. pose proof (V_g8 rho 141 Hl) as El. unfold gs in A1, A2, A7. unfold gl in A4, A5, A7.
  rewrite Eg in A1. rewrite El in A4.
  pose proof (V_opd rho HZ HN) as Vo. pose proof (V_last rho HZ HN) as Vl.
  rewrite Vo in A1. rewrite Vo in A2. rewrite Vl in A4. rewrite Vl in A5.
  unfold add in A2, A5.
  pose proof (U_addc rho (g8 (SVar 142)) 7 _ Eg ltac:(lia) ltac:(lia)) as T1. rewrite T1 in A2.
  pose proof (U_addc rho (g8 (SVar 141)) 7 _ El ltac:(lia) ltac:(lia)) as T2. rewrite T2 in A5.

  cbn [holds branch_taken] in A7. unfold bv_ltu in A7.
  pose proof (V_shp rho 142 ltac:(lia)) as S1. pose proof (V_shp rho 141 ltac:(lia)) as S2.
  assert (Hgl : bv_unsigned (rw rho 142) < bv_unsigned (rw rho 141)).
  { destruct (Z.ltb_spec (UU rho (shp (SVar 142))) (UU rho (shp (SVar 141)))) as [Hlt|Hge];
      [rewrite S1, S2 in Hlt; lia | exfalso; apply A7; reflexivity]. }
  cbv zeta. repeat split; lia.
Qed.

Lemma bk_facts_Z : ltac2:(tb__ "0|8|
S1S6bR1Vib;Vil;Vio;A4S16S1cZ1M0S14Q40M1S2R2P12M2A2A2M3A2S1cG3S1eZ2M4Z28A2A2A2S23S0S3R3A1S2cS0S45VvB;VvL;Vlastx;A3S2aS0SbS8bS72S44G0A2S6eS4eA1A3S2bS0A1A3A3A3S14G1S2R4Vib;A2A2S25S14G1S2R5Vil;A2A2S25S14G1S2R6Vio;A2A2S25S14G1S2R7G2A2A2S25S14G1S2R8P8cA2A2S25S14G1S2R9P8dA2A2S25S16S1cR6S20Z8M5R2A2A2S16S1fR2R1A2S16S1fR1S1eG4Z3dA2A2S16S16S1cS20G5R1A2M6S21S1dS1dR6R4A2R3A2G0A2M7A2S1cG7S1dG6Z7A2A2A2S1bS17S25S1dR2G0A2R1A3A1A2A2A2A2Tl;Tc;TN;TO;TL;TB;F_;F_;F_;Frho;").
Proof.
  intros rho HZ HN HF. pose proof HZ as HZ'. unfold opZ in HZ'.
  pose proof (urange (rw rho ib)). pose proof (urange (rw rho io)). pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  apply Forall_app in HF as [HL HB].
  have_fact A1 HL (SPUle vB (g8 cur)). have_fact A3 HL (SPUle cur (SLit (2 ^ 61 - 1))). have_fact A4 HL (SPUlt cur gl).
  have_fact A5 HL (SPUle (g8 gl) lastx). have_fact A6 HL (SPUle lastx (add (g8 gl) (SLit 7))). have_fact A7 HL (SPUle gl (SLit (2 ^ 61 - 1))).
  have_fact A8 HB (SPBranch BC_NE (shpk cur 1) (shp gl)).
  rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia. rewrite (U_lit64 rho (2 ^ 61 - 1)) in A7 by lia.
  change (eval rho cur) with (rw rho 140) in A3, A4. change (eval rho gl) with (rw rho 141) in A4, A7.
  change (eval rho vB) with (rw rho ib) in A1.
  assert (Hc : bv_unsigned (rw rho 140) < 2 ^ 61) by lia. assert (Hl : bv_unsigned (rw rho 141) < 2 ^ 61) by lia.
  pose proof (V_g8 rho 140 Hc) as Ec. pose proof (V_g8 rho 141 Hl) as El. unfold cur in A1, A8. unfold gl in A5, A6, A8.
  rewrite Ec in A1. rewrite El in A5. pose proof (V_last rho HZ HN) as Vl. rewrite Vl in A5. rewrite Vl in A6.
  unfold add in A6. pose proof (U_addc rho (g8 (SVar 141)) 7 _ El ltac:(lia) ltac:(lia)) as T2. rewrite T2 in A6.

  cbn [holds branch_taken] in A8. unfold bv_eqb in A8. apply negb_true_iff in A8. apply Z.eqb_neq in A8.
  pose proof (V_shp rho 141 ltac:(lia)) as S2. rewrite S2 in A8.
  unfold shpk, add in A8.
  rewrite (U_addc rho (SVar 140) (SHB + 1) (bv_unsigned (rw rho 140)) eq_refl) in A8 by (unfold SHB; lia).
  cbv zeta. repeat split; try lia.
Qed.
End LoopZ.

Ltac split_mid HF HX HT :=
  cbn [ax_S ss_facts mid_state mkA] in HF; apply Forall_app in HF as [HX HT].

Lemma FT_Z : ltac2:(tb__ "0|1|
S1S23S0S3R1A1S41A3S16S6bR2PfP10P11A4S16S6bR2P13P34P35A4S16S1cZ1S14Q40S2R2P12A2A2M0A2S1cG0S1eZ2Z28A2A2A2A2A2F_;Frho;").
Proof.
  intros rho HF. unfold FT in HF. apply Forall_app in HF as [_ HB].
  destruct (base_mc_Z rho HB) as (ZD & ZS & ZN & _). auto.
Qed.

Lemma opZ_sub : ltac2:(tb__ "0|1|
S1S3cS26S26S26S82R3S38A2M0G0G0S17S28S3eR7S38A2S29A3S6bR9R7R6R5A4S6bS3bRaR9A2R8R7R6A4F_;F_;F_;F_;F_;Fio;Fil;Fib;Fs;Frho;").
Proof.
  intros rho s ib il io Hb Hl Ho Hid HZ.
  assert (E : forall v, (v < NF)%positive -> rw (rho_sub rho s) v = rw rho v).
  { intros v Hv. rewrite rw_sub, (wsub_get_id s NF v Hid Hv). reflexivity. }
  unfold opZ in *. cbv zeta in *.
  rewrite (E ib Hb), (E il Hl), (E io Ho), (E 18%positive eq_refl). exact HZ.
Qed.

Section Glue.
Variable rho : valuation.

Lemma glue_Ls_in : ltac2:(tb__ "0|0|
S23S0S3Vrho;A1S6S2fS5fA1A1A3S23S0S3S3bVrho;S58A2A1S45S5aS5cS52A3A3F_;").
Proof.
  intros HF. unfold E_Ls_in in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (in_facts_Z 19 52 53 rho ZS ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZS as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ls_in).
  assert (ZS' : opZ rho' 19 52 53) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E52 : rw rho' 52 = rw rho 52) by reflexivity. assert (E53 : rw rho' 53 = rw rho 53) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 19)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 53)) as R53.
  apply (F_L_intro 19 52 53 rho' ZS' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E19, ?E52, ?E53; unfold HSE in *; lia.
Qed.

Lemma glue_Ls_bk : ltac2:(tb__ "0|0|
S23S0S3Vrho;A1S6S2fS5eA1A1A3S23S0S3S3bVrho;S57A2A1S45S5aS5cS52A3A3F_;").
Proof.
  intros HF. unfold E_Ls_bk in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (bk_facts_Z 19 52 53 rho ZS ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZS as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ls_bk).
  assert (ZS' : opZ rho' 19 52 53) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_Ls_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E52 : rw rho' 52 = rw rho 52) by reflexivity. assert (E53 : rw rho' 53 = rw rho 53) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 19 52 53 rho' ZS' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E19, ?E52, ?E53, ?E141; unfold HSE in *; try lia.
Qed.

Lemma glue_Ld_in : ltac2:(tb__ "0|0|
S23S0S3Vrho;A1S6S2fS5dA1A1A3S23S0S3S3bVrho;S56A2A1S45S59S5bS51A3A3F_;").
Proof.
  intros HF. unfold E_Ld_in in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (in_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ld_in).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 15)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 17)) as R17.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E15, ?E16, ?E17; unfold HSE in *; lia.
Qed.

Lemma glue_Ld_bk : ltac2:(tb__ "0|0|
S23S0S3Vrho;A1S6S2fS4fA1A1A3S23S0S3S3bVrho;S55A2A1S45S59S5bS51A3A3F_;").
Proof.
  intros HF. unfold E_Ld_bk in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (bk_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ld_bk).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_Ld_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E15, ?E16, ?E17, ?E141; unfold HSE in *; try lia.
Qed.

Lemma meas_Ls_in : ltac2:(tb__ "0|0|
S17S15Q40A1S4S3bVrho;S58A2S44A2S4Vrho;S49A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ls_bk : ltac2:(tb__ "0|0|
S17S15Q40A1S4S3bVrho;S57A2S44A2S4Vrho;S6dS44S9Z1A1A2A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ld_in : ltac2:(tb__ "0|1|
S17S15Q40A1S4S3bVrho;S56A2S6dS44S9S1eZ2Z3eA2A1M0A2A2S4Vrho;S6dS49G0A2A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ld_bk : ltac2:(tb__ "0|2|
S23S0S3Vrho;A1S6S2fS4fA1A1A3S1cS14Q40M0S4Vrho;S6dS44S9S1dS1eZ2Z3eA2M1Z1A2A1A2A2A2S14G0S4S3bVrho;S55A2S6dS44S9G1A1A2A2A2A2F_;").
Proof.
  intros HF. unfold E_Ld_bk in HF. split_mid HF HX HT. apply Forall_app in HX as [HL _].
  have_fact A3 HL (SPUle cur (SLit (2 ^ 61 - 1))). rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia.
  change (eval rho cur) with (rw rho 140) in A3. pose proof (urange (rw rho 140)) as R140.
  assert (E1 : bv_unsigned (rw (rho_sub rho s_Ld_bk) 140) = bv_unsigned (rw rho 140) + 1).
  { rewrite rw_sub. cbn [wsub_get s_Ld_bk Pos.eqb]. unfold add, cur. apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  unfold add, cur.
  rewrite (U_addc rho (SVar 140) (2 ^ 62 + 1) (bv_unsigned (rw rho 140)) eq_refl) by lia.
  rewrite (U_addc (rho_sub rho s_Ld_bk) (SVar 140) (2 ^ 62) (bv_unsigned (rw rho 140) + 1) E1) by lia.
  lia.
Qed.
End Glue.

Lemma FT_of_E : ltac2:(tb__ "0|0|
S46S31S1S23S0S3R1A1S6S2fS46A1A1A3S23S0S3R2A1S41A3F_;Fr;TE;").
Proof. intros E r HF. cbn [ax_S ss_facts E_src mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst : ltac2:(tb__ "0|0|
S1S23S0S3R1A1S6S2fS47A1A1A3S23S0S3R2A1S41A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_dst mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Ereal : ltac2:(tb__ "0|0|
S1S23S0S3R1A1S6S2fS4bA1A1A3S23S0S3R2A1S41A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_real mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Lemma next_E : ltac2:(tb__ "0|0|
S16S81S38S5S2fS46A1A1A2S16S81S38S5S2fS47A1A1A2S81S38S5S2fS4bA1A1A2A2A2").
Proof. repeat split; cbv; congruence. Qed.
Lemma FT_of_E_cls : ltac2:(tb__ "0|0|
S27S0A1S1S23S0S3R1A1S6S2fS78R2S46A2A1A1A3S23S0S3R2A1S41A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_src mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst_cls : ltac2:(tb__ "0|0|
S27S0A1S1S23S0S3R1A1S6S2fS78R2S47A2A1A1A3S23S0S3R2A1S41A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_dst mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Definition clsZ (rho : valuation) (ib il : positive) : Prop := ltac2:(tb__ "0|2|
S18S1cS6fS14Q40M0S2Vrho;Vib;A2A2M1A2S1cS1dG1S14G0S2Vrho;Vil;A2A2A2S21S12Z8A2A2A2").
Lemma hi_fact_holds : ltac2:(tb__ "0|0|
S1S26S1cS6fS14Q40S2R2R1A2A2A2S23S0S3R3A1S2aS0S64S7R2A1A1S2bS0A1A3A3F_;Fib;Frho;").
Proof. intros rho ib H. constructor; [|constructor]. unfold hi_fact. cbn [holds]. rewrite (U_lit64 rho HSE) by (unfold HSE; lia). exact H. Qed.
Lemma lo_fact_holds : ltac2:(tb__ "0|1|
S1S26S26S1cS1dS14Q40M0S2R3R2A2A2S14G0S2R3R1A2A2A2S21S12Z8A2A2S23S0S3R4A1S2aS0S65S7R3A1S7R2A1A2S2bS0A1A3A3F_;Fil;Fib;Frho;").
Proof.
  intros rho ib il H. pose proof (urange (rw rho ib)). pose proof (urange (rw rho il)). constructor; [|constructor]. unfold lo_fact, add. cbn [holds].
  rewrite (U_add2 rho (SVar ib) (SVar il) (bv_unsigned (rw rho ib)) (bv_unsigned (rw rho il)) eq_refl eq_refl) by (unfold SHB in H; lia).
  rewrite (U_lit64 rho (SHB - 8)) by (unfold SHB; lia). exact H.
Qed.

Lemma FTbT1 : ltac2:(tb__ "0|0|
S30S3fS30R1S87A3S17S28S40S0S8S5S2fS7eS69S86S32R2A1S46S62A5A1A1A1S41A3S29A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 FT_below_T). Qed.
Lemma FTbT2 : ltac2:(tb__ "0|0|
S30S3fS30R1S87A3S17S28S40S0S8S5S2fS7eS67S86S32R2A1S47S60A5A1A1A1S41A3S29A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 (proj2 FT_below_T)). Qed.
Lemma FTbT3 : ltac2:(tb__ "0|0|
S30S3fS30R1S8cA3S17S28S40S0S8S5S2fS7eS68S8dS32R2A1S4bS61A5A1A1A1S41A3S29A3F_;FL;").
Proof. intros L [<-|[<-|[]]]; [exact (proj1 (proj2 (proj2 FT_below_T))) | exact (proj2 (proj2 (proj2 FT_below_T)))]. Qed.

Section Sum.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ltac2:(tb__ "0|0|
S37S11Vok;VJ;A3").
Hypothesis Hst : stableA segs NF J.

Hypothesis HclsD : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Lemma cfg_mc_sound : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S31S3fS31R1S63A3S1S75S11Vok;S33S11S79S1SaS38R6R1A3Lr;VJ;A2R3R1R4A5S34S11VJ;S38R5R4S42A6A4FrhoT;F_;FT;Ftp;Frho;").
Proof.
  intros rho tp T HinT rhoT.
  destruct ids_mc as (I1 & I2 & I3 & I4).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  apply (cfg_soundA segs FUELM cutpcs_mc NF cuts_mc exits_mc (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_mc) tp HokG HstG check_mc); [|exact HinT].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - apply exit_postA. in_nth 0.
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA ok J NF rho tp E_real Pre_memcpyA s_real R_real Posts_memcpyA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             cuts_mc _ Hok).
    + intros ok' Jq rho1 tp1 Ho Hs. exact (memcpy_sumA ok' Jq rho1 tp1 Ho Hs).
    + intros L [<-|[<-|[]]]; [in_nth 4 | in_nth 5].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ls_in CLs_0 (F_L vBs vLs lasts) s_Ls_in tp);
      [in_nth 6 | exact ent_Ls_in | exact I1 | exact HstG | exact FLs_below | intros r tp' tr md _ HF; exact (glue_Ls_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ls_bk CLs_0 (F_L vBs vLs lasts) s_Ls_bk tp);
      [in_nth 6 | exact ent_Ls_bk | exact I2 | exact HstG | exact FLs_below | intros r tp' tr md _ HF; exact (glue_Ls_bk r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ld_in CLd_0 (F_L vBd vLd lastd) s_Ld_in tp);
      [in_nth 7 | exact ent_Ld_in | exact I3 | exact HstG | exact FLd_below | intros r tp' tr md _ HF; exact (glue_Ld_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ld_bk CLd_0 (F_L vBd vLd lastd) s_Ld_bk tp);
      [in_nth 7 | exact ent_Ld_bk | exact I4 | exact HstG | exact FLd_below | intros r tp' tr md _ HF; exact (glue_Ld_bk r HF)].
Qed.

Theorem memcpy_icpt_sum1 : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S75S11Vok;S33S11VJ;S4cR2R1A5S34S11VJ;S38R2R1S42A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc1). left; reflexivity.
Qed.

Theorem memcpy_icpt_sum2 : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S75S11Vok;S33S11VJ;S4dR2R1A5S34S11VJ;S38R2R1S42A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc2). right; left; reflexivity.
Qed.
End Sum.

Lemma etriple_SPA_pure' : ltac2:(tb__ "0|2|
S35S31S1S27S15Q40A1A1M0S74OF_;S27S3aA1M1S39R7R5R4R2R1A4S73S11S33S11S1G0G1S39S16RcR4R3R2R1A4S16S17G1R2R7A3S17S39R1R6A3A2A2Lm;Lt;Lp;Lr;R7R6R5A5R4A3F_;Fmd;Ftr;S73S11S33S11R6R5R4R3A5R2A3F_;FQ;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp Q H w [Hsm Hk]. destruct w as [tr [ms md]]. apply (H tr md Hk). split; [exact Hsm|]. cbn. auto.
Qed.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Hypothesis HclsD : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma cfg_mc_complete : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S77S3fS77R1S6aA3S1S73S11S33S11S79S1SaS38R6R1A3Lr;VJ;A2S7aR3A1R1R4A5S34S11VJ;S38R5R4S42A6A3FrhoT;F_;Fn;Ftp;Frho;").
Proof.
  intros rho tp n HinT rhoT.
  destruct ids_mc as (I1 & I2 & I3 & I4).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  apply (cfg_complete_autoIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_mc) tp HstG); [ | exact echeck_mc | | exact HinT].
  { intros m Hm. unfold vcuts_mc in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - apply (eexit_post_IA0 segs J NF rho vcuts_mc Posts_mc (mkVNA P_icpt 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_hi 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_lo 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_hi 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_lo 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA_ex J NF rho tp E_real Pre_memcpyA s_real R_real Posts_memcpyA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             vcuts_mc _ (mkVNA E_real 40 (SLit (2 ^ 63 + 8))) eq_refl).
    + intros Jq rho1 tp1 Hs. exact (memcpy_sumA_ex Jq rho1 tp1 Hs).
    + intros L [<-|[<-|[]]].
      * exists (mkVNA T3a 39 (SLit (2 ^ 63 + 8))). split; [in_nth 4|]. split; [reflexivity|]. meas_lit.
      * exists (mkVNA T3b 39 (SLit (2 ^ 63 + 8))). split; [in_nth 5|]. split; [reflexivity|]. meas_lit.
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ls_in 151 gs) (mkVNA CLs 150 cur) (F_L vBs vLs lasts) CLs_0 s_Ls_in tp);
      [in_nth 6 | reflexivity | exact ent_Ls_in | exact I1 | exact HstG | exact FLs_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ls_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ls_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ls_bk 151 (add cur (SLit 1))) (mkVNA CLs 150 cur) (F_L vBs vLs lasts) CLs_0 s_Ls_bk tp);
      [in_nth 6 | reflexivity | exact ent_Ls_bk | exact I2 | exact HstG | exact FLs_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ls_bk r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ls_bk r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ld_in 101 (add gs (SLit (2 ^ 62)))) (mkVNA CLd 100 (add cur (SLit (2 ^ 62)))) (F_L vBd vLd lastd) CLd_0 s_Ld_in tp);
      [in_nth 7 | reflexivity | exact ent_Ld_in | exact I3 | exact HstG | exact FLd_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ld_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ld_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ld_bk 101 (add cur (SLit (2 ^ 62 + 1)))) (mkVNA CLd 100 (add cur (SLit (2 ^ 62)))) (F_L vBd vLd lastd) CLd_0 s_Ld_bk tp);
      [in_nth 7 | reflexivity | exact ent_Ld_bk | exact I4 | exact HstG | exact FLd_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ld_bk r HF) | right; split; [cbn [vna_var]; exact (meas_Ld_bk r HF) | cbn; lia]]
      | cbn; lia | cbn; lia].
Qed.

Theorem memcpy_icpt_sum1_ex : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S73S11S33S11VJ;S4cR2R1A5S34S11VJ;S38R2R1S42A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc1 with (vna_state (mkVNA Pre_mc1 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). left; reflexivity.
Qed.

Theorem memcpy_icpt_sum2_ex : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S73S11S33S11VJ;S4dR2R1A5S34S11VJ;S38R2R1S42A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc2 with (vna_state (mkVNA Pre_mc2 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). right; left; reflexivity.
Qed.
End SumEx.

Lemma soff_var' : ltac2:(tb__ "0|1|
S1S26S1fS14Q40M0S2R2R1A2A2S1eZ2Z3fA2A2S17S25SfR3S7R2A1A2S14G0S2R3R2A2A2A3F_;Fi;Frho;").
Proof.
  intros rho i Hi. unfold soff. cbn [eval]. rewrite bv_signed_U.
  destruct (Zsigned_spec (bv_unsigned (rw rho i))) as [[_ X]|[Y X]]; [exact X|]. pose proof (urange (rw rho i)). lia.
Qed.

Section Public.
Variable rho : valuation.
Let a := bv_unsigned (eval rho dst). Let b := bv_unsigned (eval rho src). Let n := bv_unsigned (rw rho 18).

Lemma pre_disjoint : ltac2:(tb__ "0|1|
S27S15Q40A1A1M0S74S18S33S11S1G0S27S3aA1S39S1aL_;L_;L_;L_;S43Vrho;R2R1A6S19S35S35S33S11R1S43Vrho;R3R2A6LJ;A2A2S1fVn;S1eZ2Z3fA2A2S18S1cS1dVa;Vn;A2Vb;A2S18S1cS1dVb;Vn;A2Va;A2S17S25Vn;Z0A3A2A2F_;F_;Fw;Ftp;").
Proof.
  intros tp w HS Hn.
  assert (Hsm : smatchA segs rho tp Pre_mc0 w) by (destruct HS as [[H _]|[J [H _]]]; exact H).
  destruct Hsm as (Hsm & _). destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _).
  cbn [ss_objs ax_S Pre_mc0 mkA objs_mc app pairwise_disjoint] in Hpd.
  destruct Hpd as (_ & _ & HD & _). apply Forall_inv in HD.
  unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, O_dst, O_src in HD. cbn [ob_base ob_lo ob_hi fst snd] in HD.
  rewrite !soff_lit_small in HD by lia.
  assert (Es : soff rho vN = n) by (unfold vN; apply soff_var'; subst n; lia). rewrite !Es in HD.
  subst a b. lia.
Qed.

Lemma pre_Z : ltac2:(tb__ "0|5|
S23S0S3Vrho;A1S48A3S16S17S25Va;S1dS14Q40M0S2Vrho;PfM1A2A2S14G0S2Vrho;P11M2A2A2A2A3S16S17S25Vb;S1dS14G0S2Vrho;P13M3A2A2S14G0S2Vrho;P35M4A2A2A2A3S16S6bVrho;G1P10G2A4S16S6bVrho;G3P34G4A4S16S1cZ1Vn;A2S1cVn;S1eZ2Z28A2A2A2A2A2A2A2F_;").
Proof.
  intros HF. destruct (base_mc_Z rho HF) as (ZD & ZS & ZN & _).
  split; [exact (V_opd 15 16 17 rho ZD ZN)|]. split; [exact (V_opd 19 52 53 rho ZS ZN)|]. auto.
Qed.

Lemma xor_fact_Z : ltac2:(tb__ "0|0|
S10S25S17S25S14Q40S4Vrho;R2A2A2R1A3S1cS1dR2Vn;A2S21S1eZ2Z40A2Z1A2A2S3Vrho;ScSbS8aSdS88R4S9ZffffffffffffffffA1A3S70A3A1A2F_;F_;Fx;Fe;").
Proof.
  intros e x He Hx. cbn [holds branch_taken]. unfold bv_ltu.
  rewrite (U_xor_m1 rho e 18446744073709551615 eq_refl). rewrite He. change (eval rho vN) with (rw rho 18).
  unfold M64v. rewrite Z.ltb_lt. subst n. lia.
Qed.

Lemma facts1 : ltac2:(tb__ "0|1|
S23S0S3Vrho;A1M0S48A3S1cS1dVa;Vn;A2Vb;A2S23S0G0S2aS0S53S4aA3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 53)).
  pose proof (urange (rw rho 18)). unfold ord1, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho dst vN a n eq_refl eq_refl) by (subst a n; lia). fold b. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma facts2 : ltac2:(tb__ "0|1|
S23S0S3Vrho;A1M0S48A3S1cS1dVb;Vn;A2Va;A2S23S0G0S2aS0S54S4aA3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 53)).
  pose proof (urange (rw rho 18)). unfold ord2, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho src vN b n eq_refl eq_refl) by (subst b n; lia). fold a. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma F1_below : ltac2:(tb__ "0|0|
S17S28S40S0S8S5S2fS43A1A1A1S2aS0S53S4aA3A3S29A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2_below : ltac2:(tb__ "0|0|
S17S28S40S0S8S5S2fS43A1A1A1S2aS0S54S4aA3A3S29A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SPA_cases : ltac2:(tb__ "0|0|
S35S27S15Q40A1A1S74S33S11R3S43Vrho;R2R1A6S18S33S11R4S4cVrho;R3R2A6S33S11R4S4dVrho;R3R2A6A2F_;Fw;Ftp;FJ;").
Proof.
  intros J tp w Hw. pose proof (SPA_facts_hold segs J rho Pre_mc0 tp w Hw) as HF. cbn [ax_S ss_facts Pre_mc0 mkA] in HF.
  destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN).
  destruct (pre_disjoint tp w (or_intror (ex_intro _ J Hw)) ltac:(lia)) as [H|[H|H]]; [left | right | exfalso; lia].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts1 HF H) | exact F1_below].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts2 HF H) | exact F2_below].
Qed.
End Public.

Theorem memcpy_icpt_sum : ltac2:(tb__ "0|2|
S74OF_;S35S1S27S15Q40A1A1M0S37S11R4R3A3S36S11S38R4A3S1G0S27S3aA1M1S39R9R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S1G0G1S39RaR4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;S75S11R8S33S11R7S43R6R5A5S34S11R7S38R6R5S42A6A4F_;F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HD HS.
  eapply triple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply triple_disj; [apply memcpy_icpt_sum1 | apply memcpy_icpt_sum2]; assumption.
Qed.

Theorem memcpy_icpt_sum_ex : ltac2:(tb__ "0|2|
S35S1S27S15Q40A1A1M0S36S11S38R3A3S1G0S27S3aA1M1S39R8R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S1G0G1S39R9R4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;S73S11S33S11R6S43R5R4A5S34S11R6S38R5R4S42A6A3F_;F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HD HS.
  eapply etriple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply etriple_disj; [apply memcpy_icpt_sum1_ex | apply memcpy_icpt_sum2_ex]; assumption.
Qed.
End Icpt_memcpy_proof.

(* [comment removed for export] *)
Module Asan_memsetZ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "bool"; "true"; "app"; "None"; "Some"; "false"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "cell"; "mkCell"; "sprop"; "sobj"; "DUnknown"; "mkObj"; "SPUle"; "SAlu"; "FcsrFrm0"; "SPBranch"; "mkSS"; "DImage"; "SPAlign"; "SPNot"; "DZero"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "tv"; "dst"; "vLd"; "vBd"; "cur"; "gl"; "gs"; "F8of"; "vOd"; "O_rtc3"; "hi_fact"; "lastd"; "lo_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "la_state"; "entailsA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "vN"; "shp"; "add"; "O_rtc2"; "P_ret"; "shpk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_XOR"; "BC_GEU"; "BC_LTU"; "BC_NE"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memsetZ"; "E_real"; "E_reg"; "R_reg"; "mid_state"; "s_reg"; "E_L_bk"; "E_L_in"; "FT"; "P_ms"; "R_real"; "X_ms"; "l_regs"; "objs_ms"; "s_real"; "spm"; "CL"; "CL_0"; "E_reg_hi"; "E_reg_lo"; "FUELS"; "Pre_ms1"; "T1"; "T3"; "base_ms"; "cutpcs_ms"; "F_L"; "O_cstk"; "O_dst"; "O_frame"; "O_realms"; "O_rest"; "Pre_ms0"; "cuts_ms"; "exits_ms"; "frame_cells"; "mid_regs"; "s_L_bk"; "s_L_in"; "vDp"; "vcuts_ms"; "vexits_ms"; "xor_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memsetZ.AMSZAddr"; "l_head"; "musl_memset"; "ms_entry"; "ms_ret"; "ra_real"; "ra_reg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "NPOST"; "post_regs"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "segs"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "Pre_rip_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module AMSZAddr.
  Definition ms_entry : Z := 0x5ce7c.
  Definition ms_ret : Z := 0x5cf3c.
  Definition ra_reg : Z := 0x5d064.
  Definition ra_real : Z := 0x5cf18.
  Definition l_head : Z := 0x5d038.
  Definition musl_memset : Z := 0xdb004.
End AMSZAddr.
Import AMSZAddr.

Definition X_ms : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SdSdA2M0S1SdSdS24S23A4S3G0A1A3").

Definition O_realms : sobj := ltac2:(tb__ "0|1|
S15SfZ0A1SfZe6780A1M0SfZe6788A1S0S10S11G0Z8SfS71A1A3S3S10A1A3S14A5").

Definition frame_cells : list cell := ltac2:(tb__ "0|1|
S0S10S11SfN38A1Z8M0SeP29A1A3S0S10S11SfN30A1G0SeP28A1A3S0S10S11SfN28A1G0SeP27A1A3S0S10S11SfN20A1G0SeP26A1A3S0S10S11SfN18A1G0SeP1dA1A3S0S10S11SfN10A1G0SeP1cA1A3S0S10S11SfN8A1G0SePbA1A3S3S10A1A3A3A3A3A3A3A3").
Definition O_frame (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S15SePaA1SfN850A1SfZ0A1Vcs;S14A5").
Definition spm : sv := add (SVar 10) (SLit (-2128)).
Definition O_cstk : sobj := ltac2:(tb__ "0|0|
S15S54SfN50A1SfZ0A1S3S10A1S14A5").

Definition vDp : sv := SVar 95.
Definition O_rest : sobj := ltac2:(tb__ "0|0|
S15SePaA1S6cSfN8a0A1S3S10A1S14A5").
Definition O_dst (d : odefault) : sobj := ltac2:(tb__ "0|0|
S15S22SfZ0A1S33S3S10A1Vd;A5").
Definition objs_ms (fr : list cell) (d : odefault) : list sobj := ltac2:(tb__ "0|0|
S7S13S0S13S62Vfr;A1S0S13S60S0S13S64S0S13S61Vd;A1S0S13S2aS0S13S36S0S13S63S3S13A1A3A3A3A3A3A3A3S80A3").

Definition base_ms : list sprop := ltac2:(tb__ "0|5|
S0S12S16S35S29S33A2S23A2S0S12S16S29S23A2S0S12S16S33S23A2S0S12S16S23SfS43Z2M0Z28A2A1M1A2S0S12S16SfZ1000A1S24A2S0S12S16S35S24S23A2SfS45S43G0Z2fA2Z8A2A1M2A2S0S12S16S24G2A2S0S12S1cPfZ3A2S0S12S16SfZ1A1S33A2S0S12S16S33G1A2S0S12S1cPaM3Z4A2S0S12S16SfS44S7fZ900A2A1SeG3A1M4A2S0S12S16G4SfS43G0Z3fA2A1A2S3S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xor_fact : sprop := ltac2:(tb__ "0|0|
S1dS19S41S17S3fS22SfZffffffffffffffffA1A3S33A3A1").
Definition FT : list sprop := xor_fact :: base_ms.

Definition Pre_ms0 : axst := ltac2:(tb__ "0|1|
S7dS1aS72S78S79S0S4S2SdA2M0S1S2SdUaS22A4S0G0S1S2SdUbSfZ0A1A4S0G0S1S2SdUcS33A4S3G0A1A3A3A3A2S77S18S8SdA1S52S3S10A1S14A2S5dS76SaA9S50A2").
Definition Pre_ms1 : axst := ltac2:(tb__ "0|0|
S3bS0S12S6fS3S12A1A3S65A2").
Definition P_ms : axst := ltac2:(tb__ "0|1|
S7dS1aS73S78S7bS76A1S0S4S2SdA2M0S1S2SdUaS22A4S3G0A1A3A2S77S18S8SdA1S52S3S10A1S1eA2S5dS7aSaA9S50A2").
Definition Posts_ms : list leafA := ltac2:(tb__ "0|0|
S0S2fS32S4eS8cA2S3S2fA1A3").

Definition mid_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|15|
S78S79S7S4S2SdA2M0S0G0S1S2SdU1M1S21G1A1A4S0G0S1S2SdU2S54A4S0G0S1S2SdU5M2S21G2A1A4S0G0S1S2SdU6M3S21G3A1A4S0G0S1S2SdU7M4S21G4A1A4S0G0S1S2SdU8SePaA1A4S0G0S1S2SdU9M5S21G5A1A4S0G0S1S2SdUaM6S21G6A1A4S0G0S1S2SdUbM7S21G7A1A4S0G0S1S2SdUcM8S21G8A1A4S0G0S1S2SdUdM9S21G9A1A4S0G0S1S2SdUeMaS21GaA1A4S0G0S1S2SdUfMbS21GbA1A4S0G0S1S2SdU10McS21GcA1A4S0G0S1S2SdU11MdS21GdA1A4S0G0S1S2SdU12MeS21GeA1A4S0G0S1S2SdU13MfS21GfA1A4S0G0S1S2SdU14S54A4S0G0S1S2SdU15M10S21G10A1A4S0G0S1S2SdU1cM11S21G11A1A4S0G0S1S2SdU1dM12S21G12A1A4S0G0S1S2SdU1eM13S21G13A1A4S0G0S1S2SdU1fM14S21G14A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition mid_state (pc : Z) (l : list (nat * sv)) (facts : list sprop) (d : odefault) : axst := ltac2:(tb__ "0|0|
S7dS1aVpc;S69Vl;A1S77S18S8SdA1S52S68Vd;A2S7S12Vfacts;S4dA3PbeSaA9S50A2").

Definition E_reg : axst := ltac2:(tb__ "0|1|
S49S89S0S4S2SdA2M0S1S2SdU1SfS75A1A4S0G0S1S2SdUaS22A4S0G0S1S2SdUbS33A4S0G0S1S2SdU9S22A4S0G0S1S2SdU15SfZ0A1A4S0G0S1S2SdU12S33A4S3G0A1A3A3A3A3A3A3S3S12A1S14A4").
Definition E_reg_hi : axst := ltac2:(tb__ "0|0|
S3bS0S12S2bS24A1S3S12A1A3S47A2").
Definition E_reg_lo : axst := ltac2:(tb__ "0|0|
S3bS0S12S2dS24S23A2S3S12A1A3S47A2").

Definition E_real : axst := ltac2:(tb__ "0|1|
S49S71S0S4S2SdA2M0S1S2SdU1SfS74A1A4S0G0S1S2SdUaS22A4S0G0S1S2SdUbSfZ0A1A4S0G0S1S2SdUcS33A4S3G0A1A3A3A3A3S3S12A1S14A4").

Definition F_L : list sprop := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.F_L vBd vLd lastd.
Definition l_regs (a3 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2SdA2M0S1S2SdUaS22A4S0G0S1S2SdUbSfZ0A1A4S0G0S1S2SdUcS33A4S0G0S1S2SdUdVa3;A4S0G0S1S2SdUeS34S26A1A4S3G0A1A3A3A3A3A3").
Definition CL_0 : axst := ltac2:(tb__ "0|0|
S49S70S51S34S25A1A1S3S12A1S14A4").
Definition CL : axst := ax_add_facts F_L CL_0.
Definition E_L_in : axst := ltac2:(tb__ "0|1|
S49S70S51S34S27A1M0A1S7S12S28S27P8eS22A3S7S12S28S26P8dS2cA3S0S12S1dS19S40G0S34S26A1A3A1S3S12A1A3A3A3S14A4").
Definition E_L_bk : axst := ltac2:(tb__ "0|1|
S49S70S51S38S25Z1A2M0A1S7S12S5fS0S12S19S42G0S34S26A1A3S3S12A1A3A3S14A4").

Definition s_reg : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLd) :: infer_sub 1 (ax_S E_reg) (ax_S Pre_rip)) in exact x).
Definition s_real : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 (ax_S E_real) (ax_S Pre_mszA)) in exact x).
Definition R_reg : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_reg_hi Pre_rip s_reg with Some R => R | None => [] end) in exact x).
Definition R_real : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_real Pre_mszA s_real with Some R => R | None => [] end) in exact x).
Definition T1 : axst := ltac2:(tb__ "0|0|
S3bS4dS88S4aS81S37S47S48A5A2").
Definition T3 : axst := ltac2:(tb__ "0|0|
S3bS4dS88S53S83S8bS84A1S46S4fA5A2").

Definition cuts_ms : list axst := ltac2:(tb__ "0|0|
S0S2eS5aS0S2eS5bS0S2eS5cS0S2eS55S3S2eA1A3A3A3A3").
Definition exits_ms : list axst := ltac2:(tb__ "0|0|
S0S2eS4eS0S2eS47S0S2eS46S0S2eS4cS0S2eS4bS3S2eA1A3A3A3A3A3").
Definition cutpcs_ms : list Z := ltac2:(tb__ "0|0|
S0S20S89S0S20S71S0S20S70S3S20A1A3A3A3").
Definition FUELS : nat := 600%nat.

Definition s_L_in : wsub := ltac2:(tb__ "0|1|
S0S4S1fSdA2M0S1S1fSdP8cS27A4S3G0A1A3").
Definition s_L_bk : wsub := ltac2:(tb__ "0|1|
S0S4S1fSdA2M0S1S1fSdP8cS35S25SfZ1A1A2A4S3G0A1A3").

Lemma fr_reg_hi : ltac2:(tb__ "0|1|
S3dScSbS13A1M0A1S87S57S81S4aA3S9G0S48A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_reg_lo : ltac2:(tb__ "0|1|
S3dScSbS13A1M0A1S87S58S82S4aA3S9G0S48A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_reg_hi : ltac2:(tb__ "0|0|
S3dS5S86S57S81S4aS48S7cS2fS2eS30S8aA4A5S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_reg_lo : ltac2:(tb__ "0|0|
S3dS5S86S58S82S4aS48S7cS2fS2eS30S8aA4A5S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_real : ltac2:(tb__ "0|1|
S3dScSbS13A1M0A1S87S46S83S53A3S9G0S4fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_real : ltac2:(tb__ "0|0|
S3dS5S86S46S83S53S4fS7cS2fS2eS30S85A4A5S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition vcuts_ms : list vnodeA := ltac2:(tb__ "0|1|
S0S39S3aS5aZc8SfZ0A1A3S0S39S3aS5bZ4fSfS43Z2Z3fA2M0A1A3S0S39S3aS5cZ27SfS44G0Z8A2A1A3S0S39S3aS55Z64S25A3S3S39A1A3A3A3A3").
Definition vexits_ms : list vnodeA := ltac2:(tb__ "0|4|
S0S39S3aS4eZ0SfS45S43Z2M0Z40A2Z1M1A2A1A3S0S39S3aS47Z50SfS43G0Z3fA2M2A1A3S0S39S3aS46Z28SfS44G2Z8A2A1A3S0S39S3aS4cZ65M3S27A3S0S39S3aS4bG3S35S25SfG1A1A2A3S3S39A1A3A3A3A3A3").
Lemma echeck_ms : ltac2:(tb__ "0|0|
S3dS5S8dS7eS59S5eS76S6dS6eA6S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_ms : ltac2:(tb__ "0|0|
S3dS5S3cS7eS59S5eS76S66S67A6S6A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELS cutpcs_ms NF vcuts_ms vexits_ms cuts_ms exits_ms eq_refl eq_refl echeck_ms). Qed.

Lemma ent_L_in : ltac2:(tb__ "0|0|
S3dS5S31S4cS56S6bA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_L_bk : ltac2:(tb__ "0|0|
S3dS5S31S4bS56S6aA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Asan_memsetZ.

(* [comment removed for export] *)
Module DrvFp.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "nil"; "bool"; "option"; "Some"; "true"; "nat"; "prod"; "cons"; "pair"; "app"; "length"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sv"; "sstate"; "sprop"; "SLit"; "rl"; "ss_objs"; "cell"; "holds"; "ob_dflt"; "rw"; "DList"; "ob_base"; "ob_cells"; "ob_hi"; "ob_lo"; "agree_below"; "obj_holds"; "obj_range"; "odefault"; "outside_all"; "rm"; "smatch"; "SAlu"; "SVar"; "dflt_writable"; "is_arr"; "mkObj"; "sprop_below"; "ss_facts"; "ss_lenient"; "swf"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "FdChannel"; "WriteEv"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface"; "MSG_REF"; "facts_fp"; "Pre_ref"; "Posts_ref"; "P_ref"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.DrvFp.Fp"; "Kwr"; "Kf"; "EVSr"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "ax_base"; "mkLeafA"; "sym_runA"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.DrvFp.Fp.Inst"; "rho_wl"; "Jp"; "oext"; "f6"; "rho_fin"; "WLF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err.WLerrS"; "Pre_wl2"; "D"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "set_rl"; "obj_nolist"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err.WLerr"; "Kw"; "MSG"; "Posts_wl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates"; "CUTS_FP"; "FUEL_FP"; "O_b2e"; "unlist_at"; "XP1"; "XP2"; "splits_fp"; "unk_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "beval"; "cells_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates"; "axc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "to_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundI SymSoundM SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj SymCall SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SysA MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import SpecConsts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvFw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma obj_holds_unlist : ltac2:(tb__ "0|0|
S10S61S11S46SdS24S1aR2A1S1cR1A1A3SdS0S18A1S1eR3A1S1S18A1A3S22S33R6R5R4A4S22S33R7R6S74R5A1A4F_;F_;F_;Fl;Fo;Fms;Frho;").
Proof.
  intros rho ms o l Hd Hc (Hb & Hw & Hcl & Hdf & Hi). unfold unk_obj, obj_holds. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi].
  split; [exact Hb|]. split; [intros off Hoff _; apply Hw; [exact Hoff | rewrite Hd; reflexivity]|].
  split; [constructor|]. split; [|exact I].
  intros off Hoff _. cbn. rewrite Hd in Hdf. cbn in Hdf. eexists. apply Hdf; [exact Hoff|].
  rewrite Hc. intros X. apply Exists_exists in X as (c & Hin & _). destruct Hin.
Qed.

Lemma smatch_unlist_at : ltac2:(tb__ "0|0|
S10S13S6S11S46S7S0S3bA1S62A2SdS3S11A1S6bS11S17R5A1R4A3S4S11R3A2A3SdS24S1aR4A1S1cR3A1A3SdS0S18A1S1eR5A1S1S18A1A3SdS2S30S70R8R7A2A1S5A3S27S33RaR9R5A4S27S33RbS70RaR9A2R6A4F_;F_;F_;F_;F_;Fw;Fl;Fo;Fi;FS;Frho;").
Proof.
  intros rho S i o l [tr [ms md]] Hn Hd Hc Hwf Hsm.
  pose proof (nth_error_split3 _ _ _ Hn) as Esplit.
  unfold unlist_at in Hwf |- *. rewrite Hn in Hwf |- *.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hcsr & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  assert (RNG : obj_range rho (unk_obj o) = obj_range rho o) by reflexivity.
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hcsr|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs set_objs]. destruct Hm as (Hall & Hpd & Hfr). rewrite Esplit in Hall, Hpd, Hfr.
  split; [|split].
  - apply Forall_app in Hall as [HA HB]. inversion HB; subst. apply Forall_app. split; [exact HA|].
    constructor; [eapply obj_holds_unlist; eauto | assumption].
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd. rewrite map_app in Hpd |- *. cbn [map] in Hpd |- *. rewrite RNG. exact Hpd.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. rewrite Forall_app in Hout |- *. destruct Hout as [HA HB].
    split; [exact HA|]. inversion HB; subst. constructor; [rewrite <- RNG; assumption | assumption].
Qed.

Section Fp.
Variable ok : assn.
Variable J0 : jpredA.

Definition EVSr (k : nat) : list event := ltac2:(tb__ "0|1|
S4cS31Q8A1M0S3bS3eS64A1S4eG0Vk;S41A3A4").
Definition Kwr (k : nat) : jpredA := ltac2:(tb__ "0|1|
S10S0S31Q40A1A1S0S3bA1M0S3aSfG0G0SeVJ0;R5R4R1R2A4SdG0R3SaS3bR1S4bVk;A1A3A3A2Ltr0;A2Lmd;Ltr;Lt;Lr;").

Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd2 : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S0S3bA1S3aVJ0;R4R3R2R1A4SdS3S3cA1S3fS40R2A1S64A2S4S3cS3dS64A1A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HokK : ltac2:(tb__ "0|0|
S6S38S33Vok;S49R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S6S7aS33Vok;S49R1A1A3Fk;").

Definition Kf (r1 : valuation) (tp : list word) (k : nat) : jpredA := ltac2:(tb__ "0|1|
S10S0S31Q40A1A1M0S0S3bA1S3aSeSdG0R3Vtp;A3S49Vk;Vr1;R3R2R1A5A2Lmd;Ltr;Lt;L_;").
Lemma J0_mat : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S0S3bA1S3aS3aS88S33R4R2R1A4VJ0;R6R5R4R3A4VJ0;R7R6R5R3A4F_;F_;Fmd';Fmd;Ftr;Ft;Fr;").
Proof. intros r t tr md md' Hme HJ. eapply Hst0; [apply agree_below_refl | exact Hme | exact HJ]. Qed.
Lemma Kf_stable : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S6S46S39S33R1S4aR4R3R2A3A3Flvl;Fk;Ftp;Fr1;").
Proof.
  intros r1 tp k lvl r r' t tr md md' Hag Hme [Ht (tr0 & HJ & Htr)]. split; [exact Ht|].
  exists tr0. split; [eapply J0_mat; eauto | exact Htr].
Qed.
Lemma Kf_okK : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S6S38S33Vok;S4aR3R2R1A3A3Fk;Ftp;Fr1;").
Proof. intros r1 tp k r t tr ms md msv' [_ HK]. exact (HokK k r1 t tr ms md msv' HK). Qed.
Lemma Kf_okP : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S6S7aS33Vok;S4aR3R2R1A3A3Fk;Ftp;Fr1;").
Proof. intros r1 tp k r t tr ms md x8 [_ HK]. exact (HokP k r1 t tr ms md x8 HK). Qed.
Lemma Kw0_of_J0 : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S0S3bA1S3aVJ0;R4R3R2R1A4S49U0R5R4R3R2A5F_;Fmd;Ftr;Ft;Fr;").
Proof. intros r t tr md HJ. exists tr. split; [exact HJ|]. unfold EVSr. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma okK_J0 : ok_frameA segs ok J0.
Proof. intros r t tr ms md msv' HJ. exact (HokK 0%nat r t tr ms md msv' (Kw0_of_J0 _ _ _ _ HJ)). Qed.

Section Inst.
Variable W : axst. Variables S6 Cs : sstate. Variable o8 : sobj. Variable bl : list bexp. Variable s : wsub. Variable R : list sobj.
Variables T Tf F : axst. Variables G1 G2 G2u G3 : sstate. Variable sp : wsub. Variable EX : list sprop.
Hypothesis HrunW : ltac2:(tb__ "0|1|
SdS3S0S4fA1M0A1S54S75S6eS6dS43S5A5S4G0S8S4fS53VW;S79A2S1S4fA1A3A2A3").
Hypothesis HnW : ss_next (ax_S W) = 116%positive.
Hypothesis HXW : ax_X W = X_ref.
Hypothesis HbW : ltac2:(tb__ "0|0|
SdS12S52VW;A1S15S34A1A3").
Hypothesis HfW : ltac2:(tb__ "0|0|
SdS0S14A1S2eS50VW;A1A1SaS14VEX;S42A3A3").
Hypothesis Hsplits : ltac2:(tb__ "0|0|
SdS3S13A1S73S50VW;A1A1S4S13VS6;A2A3").
Hypothesis Hfinish : finish_fp S6 = Cs.
Hypothesis Hnl6 : state_nolist S6 = true.
Hypothesis Hrl5 : state_has_rl 5 S6 = false.
Hypothesis Ho8 : ltac2:(tb__ "0|0|
SdS3S11A1S6bS11S17VS6;A1U3A3S4S11Vo8;A2A3").
Hypothesis Ho8lo : ob_lo o8 = SLit (-464).
Hypothesis Ho8hi : ob_hi o8 = SLit (-426).
Hypothesis Ho8w : ltac2:(tb__ "0|0|
SdS2S2aS1aVo8;A1A1S5A3").
Hypothesis Ho8a : ltac2:(tb__ "0|0|
SdS2S2bS1aVo8;A1A1ScA3").
Hypothesis Hcb : ltac2:(tb__ "0|2|
SdS3S0S76A1M0A1S78S1eVo8;A1S15N1d0M1A1Z0S8cS8bN1aaG1A2A1A4S4G0Vbl;A2A3").
Hypothesis Hbl : ltac2:(tb__ "0|1|
S10SdS0S31Q8A1M0A1S4cS76G0S77R1A1Vbl;A4S41A3Fr;").
Hypothesis HswfC : swf Cs = true.
Hypothesis HnC : ss_next Cs = 116%positive.
Hypothesis Hn6 : ss_next S6 = 116%positive.
Hypothesis HnL : ss_next (obj_to_list S6 3 5) = 116%positive.
Let C : axst := ax_setS W Cs.
Hypothesis Hefr : ltac2:(tb__ "0|1|
SdS3S0S11A1M0A1S86VC;S5dVs;A3S4G0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
SdS2S85VC;S5dVs;VR;S8S51S5eS1S51A1A3A5S5A3").
Hypothesis S13 : wsub_get s 13 = SLit 38.
Hypothesis S15 : wsub_get s 15 = SLit 0.
Hypothesis HT : ltac2:(tb__ "0|0|
SdS51S87Vs;S5dS5eVC;VR;A5VT;A3").
Hypothesis HnT : ss_next (ax_S T) = 141%positive.
Hypothesis HTf : ltac2:(tb__ "0|0|
SdS51S84S42VT;A2VTf;A3").
Hypothesis HlTf : ltac2:(tb__ "0|0|
SdS2S2fS50VTf;A1A1ScA3").
Hypothesis HnTf : ss_next (ax_S Tf) = 141%positive.
Hypothesis HrunF : ltac2:(tb__ "0|1|
SdS3S0S4fA1M0A1S54S75S6eS6dVTf;S5A5S4G0S8S4fS53VF;S79A2S1S4fA1A3A2A3").
Hypothesis HbF : ltac2:(tb__ "0|0|
SdS12S52VF;A1S15S34A1A3").
Hypothesis Hxp1 : ltac2:(tb__ "0|0|
SdS3S13A1S7bS50VF;A1S71A2S4S13VG1;A2A3").
Hypothesis HobjsG1 : ltac2:(tb__ "0|1|
SdS0S11A1S17VG1;A1M0SaS11S4eS11UfG0A3S8S11S6fS1S11A1A3A3A3").
Hypothesis HnG1 : ss_next G1 = 141%positive.
Hypothesis Hdrop : drop1 G1 = G2.
Hypothesis HG2o : ltac2:(tb__ "0|0|
SdS3S11A1S6bS11S17VG2;A1U1A3S4S11S2cS28S7eS29PaA1S15N1d0A1A3S15Z0A1S15Z26A1S1S18A1S1cP5A1A5A2A3").
Hypothesis Hunl : unlist_at G2 1 = G2u.
Hypothesis HnG2u : ss_next G2u = 141%positive.
Hypothesis HswfG2u : swf G2u = true.
Hypothesis Hxp2 : ltac2:(tb__ "0|0|
SdS3S13A1S7bVG2u;S72A2S4S13VG3;A2A3").
Hypothesis HnG3 : ss_next G3 = 141%positive.
Hypothesis HnlG3 : state_nolist G3 = true.
Hypothesis Hent : ltac2:(tb__ "0|0|
SdS2S56S7fVG3;A1S45Vsp;A3S5A3").
Hypothesis Hspid : ltac2:(tb__ "0|0|
SdS2S83Vsp;S48A2S5A3").

Definition f6 (r : valuation) : positive -> list byte := ltac2:(tb__ "0|1|
S46S2S0S31Q8A1M0A1L_;S7cR1P6A2S1G0A1S16Vr;R1A2X2x2Ll;").
Definition rho_wl (r : valuation) : valuation := ltac2:(tb__ "0|0|
S80S5fVr;S5aVr;A1A2P5S41A3").
Lemma rho_wl_5 : ltac2:(tb__ "0|0|
S10SdS0S31Q8A1A1S16S57R1A1P5A2S41A3Fr;"). Proof. intros r. reflexivity. Qed.
Lemma rho_wl_6 : ltac2:(tb__ "0|1|
S10SdS0S31Q8A1M0A1S16S57R1A1P6A2S1G0A1A3Fr;"). Proof. intros r. reflexivity. Qed.
Lemma rho_wl_set : ltac2:(tb__ "0|0|
S10SdS10S57R1A1S5fR1S46S2S0S31Q8A1A1L_;S7cR1P5A2S41S5aR2R1A2X2x2Ll;A2A3Fr;").
Proof. intros r. reflexivity. Qed.

Definition WLF (r : valuation) : Prop := ltac2:(tb__ "0|3|
SeSdS0S31Q8A1M0A1M1S16Vr;P5A2S41A3SeSdG1S16Vr;P6A2S1G0A1A3SeSdS47S32Q40M2S1bVr;PdA2A2Z26A3SdS47S32G2S1bVr;PfA2A2Z0A3A2A2A2").
Definition Jp (r1 : valuation) (tp : list word) : jpredA := ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S0S3bA1S3aSeS5cR4A1S4aVr1;Vtp;U0R4R3R2R1A7A2Lmd;Ltr;Lt;Lr;").

Lemma Jp_stable : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S39S33P5cS58R2R1A2A3Ftp;Fr1;").
Proof.
  intros r1 tp r r' t tr md md' Hag Hme [(A5 & A6 & A13 & A15) HK].
  split; [| eapply (Kf_stable r1 tp 0%nat 92%positive); [exact Hag | exact Hme | exact HK]].
  destruct Hag as (Hw & Hl & _). unfold WLF.
  rewrite <- (Hl 5%positive), <- (Hl 6%positive), <- (Hw 13%positive ltac:(lia)), <- (Hw 15%positive ltac:(lia)).
  repeat split; assumption.
Qed.

Lemma Kw_Jp_Kf : ltac2:(tb__ "0|1|
S10S0S31Q40A1A1M0S6S10G0S0S3bA1S3aS65S58R7R6A2S41S1S31Q8A1A1R5R4R3R2R1A8S4aR8R7R6R5R4R3R2A7F_;Fmd;Ftr;Ft;Fr;Fk;Ftp;Fr1;").
Proof.
  intros r1 tp k r t tr md (tr0 & [_ [Ht (tr00 & HJ & ->)]] & ->). split; [exact Ht|].
  exists tr00. split; [exact HJ|]. unfold WLerr.TRk, WLerr.MSG, EVSr. cbn [firstn map app]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma MSG_len : ltac2:(tb__ "0|1|
SdS6SbS31Q8A1M0S66S41S1G0A1A2A2U26A3").
Proof. reflexivity. Qed.

Lemma wl_call : ltac2:(tb__ "0|4|
S10S0S31Q40A1A1M0S10G0S69S33Vok;S35S33S58R4R3A2M1S5dR2R1A5S36S33S65G1S41S1S31Q8A1M2A1M3SbG2S66S41G3A2A2A4P5cR2R1S67A6A4Ftp2;Frho2;Ftp;Fr1;").
Proof.
  intros r1 tp rho2 tp2.
  apply triple_SPA_pure. intros tr md [(A5 & A6 & A13 & A15) _].
  apply (triple_SPA_conseq_J segs ok _ (Jp r1 tp)); [intros t md0 (HJ & _ & _); exact HJ|].
  apply (WLerr.wl2_sum ok (Jp r1 tp) rho2 tp2 MSG_REF [] A5 A6).
  - rewrite A13. reflexivity.
  - rewrite A15. reflexivity.
  - rewrite MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros k r t tr0 ms md0 msv' HK HMI Hh Hp Hstep.
    exact (Kf_okK r1 tp k r t tr0 ms md0 msv' (Kw_Jp_Kf r1 tp k r t tr0 md0 HK) HMI Hh Hp Hstep).
  - intros k r t tr0 ms md0 x8 HK Hp Ho.
    exact (Kf_okP r1 tp k r t tr0 ms md0 x8 (Kw_Jp_Kf r1 tp k r t tr0 md0 HK) Hp Ho).
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - rewrite MSG_REF_len. lia.
Qed.

Lemma wl_call_ex : ltac2:(tb__ "0|4|
S10S0S31Q40A1A1M0S10G0S68S33S35S33S58R4R3A2M1S5dR2R1A5S36S33S65G1S41S1S31Q8A1M2A1M3SbG2S66S41G3A2A2A4P5cR2R1S67A6A3Ftp2;Frho2;Ftp;Fr1;").
Proof.
  intros r1 tp rho2 tp2 w Hw. pose proof Hw as [Hsm [(A5 & A6 & A13 & A15) HK]].
  apply (WLerr.wl2_sum_ex (Jp r1 tp) rho2 tp2 MSG_REF [] A5 A6).
  - rewrite A13. reflexivity.
  - rewrite A15. reflexivity.
  - rewrite MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - rewrite MSG_REF_len. lia.
  - exact Hw.
Qed.

Lemma SPA_splits : ltac2:(tb__ "0|0|
S37S10S0S31Q40A1A1S6aS35S33R4VW;R3R2R1A6S35S33R5S55VW;VS6;A2R4R3R2A6F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hsp. pose proof Hsplits as H. unfold splits_fp, obindW in H.
  destruct (split_obj_at (ax_S W) 0 (SLit (-584))) as [S1|] eqn:E1; [|discriminate].
  destruct (split_obj_at S1 1 (SLit (-552))) as [S2|] eqn:E2; [|discriminate].
  destruct (split_obj_at S2 2 (SLit (-464))) as [S3|] eqn:E3; [|discriminate].
  destruct (split_obj_at S3 3 (SLit (-426))) as [S4|] eqn:E4; [|discriminate].
  destruct (split_obj_at S4 5 (SLit (FERR + 120))) as [S5|] eqn:E5; [|discriminate].
  pose proof (SPA_split segs J rho W 0 (SLit (-584)) S1 tp w E1 Hsp) as H1.
  pose proof (SPA_split segs J rho (ax_setS W S1) 1 (SLit (-552)) S2 tp w E2 H1) as H2.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS W S1) S2) 2 (SLit (-464)) S3 tp w E3 H2) as H3.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS W S1) S2) S3) 3 (SLit (-426)) S4 tp w E4 H3) as H4.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS (ax_setS W S1) S2) S3) S4) 5 (SLit (FERR + 120)) S5 tp w E5 H4) as H5.
  exact (SPA_split segs J rho (ax_setS (ax_setS (ax_setS (ax_setS (ax_setS W S1) S2) S3) S4) S5) 6 (SLit (FERR + 124)) S6 tp w H H5).
Qed.

Lemma facts_rho_wl : ltac2:(tb__ "0|0|
S10S4dS14S19R1A1S42A3S4dS14S19S57R2A1A1S42A3F_;Fr;").
Proof.
  intros r H. apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) H p Hp) as X.
  unfold facts_fp in Hp. destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; exact X.
Qed.
Lemma fb_facts : ltac2:(tb__ "0|0|
SdS2S6cS14S2dS48A1S42A3S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition oext (o : sobj) : sv * sv * sv := ltac2:(tb__ "0|0|
S9S7S12S12A2S12S9S12S12S1dVo;A1S20Vo;A1A4S1fVo;A1A4").
Lemma obj_to_list_exts : ltac2:(tb__ "0|1|
S13S6S46SdS0S7S7S12S12A2S12A2M0A1S4cS11G0S59S17S8aR3R2R1A3A1A4S4cS11G0S59S17R3A1A4A3Fl;Fi;FS;").
Proof.
  intros S i l. unfold obj_to_list. destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|reflexivity].
  cbn [ss_objs set_objs].
  transitivity (map oext (firstn i (ss_objs S) ++ o :: skipn (Datatypes.S i) (ss_objs S))); [rewrite !map_app; reflexivity|].
  rewrite <- (nth_error_split3 _ _ _ Hn). reflexivity.
Qed.
Lemma obj_range_ext_rl : ltac2:(tb__ "0|0|
S10S46S0S31Q8A1A1F_;S11S11SdS12S1dR1A1S1dR2A1A3SdS12S20R2A1S20R3A1A3SdS12S1fR3A1S1fR4A1A3SdS2S60R5A1S5A3SdS7S47S47A2S23S5fR8R7A2R5A2S23R8R6A2A3F_;F_;F_;F_;Fo';Fo;Ff;Frho;").
Proof.
  intros rho f o o' E1 E2 E3 Hnl. unfold obj_nolist in Hnl.
  apply andb_prop in Hnl as [Hnl _]. apply andb_prop in Hnl as [Hnl _]. apply andb_prop in Hnl as [Hnl Hhi]. apply andb_prop in Hnl as [Hb Hlo].
  unfold obj_range, obj_lo_of, obj_hi_of, soff. rewrite E1, E2, E3. rewrite !(eval_set_rl rho f) by assumption. reflexivity.
Qed.
Lemma outside_all_oext_rl : ltac2:(tb__ "0|2|
S10S46S0S31Q8A1A1F_;S0S11A1M0G0S31Q40A1SdS0S7S7S12S12A2S12A2M1A1S4cS11G1S59R2A4S4cS11G1S59R3A4A3SdS2S6cS11S60R4A3S5A3S25R7R5R3A3S25S5fR8R7A2R5R4A3F_;F_;F_;Fx;Fobjs';Fobjs;Ff;Frho;").
Proof.
  intros rho f objs. induction objs as [|o t IH]; intros [|o' t'] x Hm Hnl Hout.
  - constructor.
  - cbn [map] in Hm. exfalso. inversion Hm.
  - cbn [map] in Hm. exfalso. inversion Hm.
  - cbn [map] in Hm. injection Hm as Eb El Eh Ht. cbn [forallb] in Hnl. apply andb_prop in Hnl as [Ho Hnt]. inversion Hout; subst.
    constructor; [| apply IH; assumption]. cbn zeta in *. rewrite (obj_range_ext_rl rho f o o' Eb El Eh Ho). assumption.
Qed.

Lemma reshape : ltac2:(tb__ "0|1|
S10S0S31Q40A1A1S10S6aS4dS14S19R2A1S42A3S35S33S4aR5R4U0M0A3VW;R3R4R2A6S35S33S4aR6R5G0A3VC;S57R4A1R5R3A6F_;F_;Fw;Frho;Ftp;Fr1;").
Proof.
  intros r1 tp rho w HF Hsp.
  pose proof (SPA_splits _ rho tp w Hsp) as H6.
  unfold C. rewrite <- (ax_setS_twice W S6 Cs).
  eapply (SPA_morphX (Kf r1 tp 0) (Kf r1 tp 0) (ax_setS W S6) Cs rho (rho_wl rho) tp w).
  - cbn [ax_X ax_base ax_setS]. rewrite HXW, HbW, HnC. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - cbn [ax_base ax_setS]. rewrite HbW. reflexivity.
  - cbn [ax_X ax_setS]. rewrite HXW. intros r [<-|[<-|[]]]; cbn [fst snd]; rewrite rho_wl_set; split; apply eval_set_rl; reflexivity.
  - cbn [ax_S ax_setS]. intros x Hout Hrm. split; [|reflexivity].
    rewrite <- Hfinish. unfold finish_fp. cbn [ss_objs app_obj]. apply outside_all_app_iff. split.
    +
      rewrite rho_wl_set. apply (outside_all_oext_rl rho _ (ss_objs S6)); [apply obj_to_list_exts | | exact Hout].
      pose proof Hnl6 as X. unfold state_nolist in X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ X]. exact X.
    + cbn [app]. unfold outside_all. constructor; [|constructor]. cbn zeta. unfold obj_range, obj_lo_of, obj_hi_of, O_b2e; cbn [ob_base ob_lo ob_hi eval fst snd].
      rewrite !soff_lit_small by lia. lia.
  - intros Hsm. rewrite <- Hfinish. unfold finish_fp.
    pose proof (smatch_set_rl segs rho (f6 rho) S6 (virt tp w) Hnl6 Hsm) as H5.
    pose proof (smatch_obj_to_list segs _ S6 (virt tp w) 3 5 o8 (-464) (-426) bl H5 Ho8 Ho8lo Ho8hi
                  ltac:(lia) ltac:(lia) Ho8w Ho8a Hcb Hrl5) as H7.
    rewrite Hbl in H7. change (rho_set_rl (set_rl rho (f6 rho)) 5 MSG_REF) with (rho_wl rho) in H7.
    unfold app_obj, O_b2e.
    apply (smatch_carve_rom segs (rho_wl rho) (obj_to_list S6 3 5) (virt tp w) 0 0 6 (ss_next (obj_to_list S6 3 5)) H7).
    + rewrite <- Hfinish in HswfC. exact HswfC.
    + lia. + lia. + lia.
    + rewrite rho_wl_6. reflexivity.
    + intros k Hk. exfalso. lia.
    + apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd]. lia.
  - intros HK. exact HK.
  - exact H6.
Qed.

Lemma W_facts : ltac2:(tb__ "0|0|
S37S10S0S31Q40A1A1S6aS35S33R4VW;R3R2R1A6S4dS14S19R4A1S42A3F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hsp. pose proof (SPA_facts_hold segs J rho W tp w Hsp) as HF. rewrite HfW in HF.
  apply Forall_app in HF as [_ HF]. exact HF.
Qed.

Definition rho_fin (rho0 rho3 : valuation) (ms : machine_state) (md : Model) (tp : list word) : valuation := ltac2:(tb__ "0|0|
S82S5fS81Vrho3;S8S11S6fS1S11A1A3S89Vmd;Vtp;Vms;A3A3S16Vrho0;A1A2Vsp;A2").

Lemma cleanup : ltac2:(tb__ "0|2|
S10S0S31Q40A1A1M0S0S3bA1M1S3aOFx2;Fx1;Fx0;Fx;S10S10G0G1S61S3aS10S10G0G1S3aRcR5R3R2R1A4RdR5R4R3R2A4F_;Fmd';Ftr';Ft;Fr';Fr;S35S33R8VF;R6R5S9G1S62R4S63R3R2A2A4A6S35S33R9S45S5bR8R7R4R3R6A5R6S9G1S62R5S63R4R3A2A4A6F_;F_;Fmd;Fms;Ftr;Ftp;Frho3;Frho0;FJ;").
Proof.
  intros J rho0 rho3 tp tr ms md HJi Hsp.
  pose proof (SPA_x_sub segs J rho3 F [] tp _ ltac:(intros r Hr; destruct Hr) Hsp) as H0.
  assert (E0 : ax_setX F [] = axc (ax_S F)) by (unfold ax_setX, axc; rewrite HbF; reflexivity). rewrite E0 in H0.
  assert (H1 : SPA segs J (axc G1) rho3 tp (tr, mkCfg ms md)).
  { apply (SPA_morph J J (axc (ax_S F)) G1 rho3 rho3 tp _ eq_refl); [cbn [ax_base axc]; rewrite HnG1; reflexivity | | intros HK; exact HK | exact H0].
    intros Hsm. exact (smatch_xforms segs XP1 rho3 (ax_S F) G1 _ Hxp1 Hsm). }
  pose proof (SPA_unobj segs J rho3 (axc G1) (firstn 15 (ss_objs G1)) [O_b2e] tp tr ms md
                HobjsG1 H1 ltac:(intros HK; exact (HJi _ _ _ _ _ HK))) as H2.
  cbn zeta in H2. cbn [ax_S axc] in H2. pose proof Hdrop as Hd. unfold drop1 in Hd. rewrite Hd in H2.
  set (rho4 := rho_absorb rho3 [O_b2e] (vms md tp ms)) in H2.
  change (ax_setS (axc G1) G2) with (axc G2) in H2.
  assert (H2u : SPA segs J (axc G2u) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_morph J J (axc G2) G2u rho4 rho4 tp _ eq_refl); [cbn [ax_base axc]; rewrite HnG2u; reflexivity | | intros HK; exact HK | exact H2].
    intros Hsm. rewrite <- Hunl. eapply (smatch_unlist_at rho4 G2 1 _ 5 _ HG2o eq_refl eq_refl); [rewrite Hunl; exact HswfG2u | exact Hsm]. }
  assert (H3 : SPA segs J (axc G3) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_morph J J (axc G2u) G3 rho4 rho4 tp _ eq_refl); [cbn [ax_base axc]; rewrite HnG3; reflexivity | | intros HK; exact HK | exact H2u].
    intros Hsm. exact (smatch_xforms segs XP2 rho4 G2u G3 _ Hxp2 Hsm). }
  assert (H4 : SPA segs J (axc G3) (set_rl rho4 (rl rho0)) tp (tr, mkCfg ms md)).
  { apply (SPA_morph J J (axc G3) G3 rho4 (set_rl rho4 (rl rho0)) tp _ eq_refl); [cbn [ax_base axc]; rewrite HnG3; reflexivity | | intros HK; apply (HJi _ _ _ _ _ HK) | exact H3].
    intros Hsm. exact (smatch_set_rl segs rho4 (rl rho0) G3 _ HnlG3 Hsm). }
  unfold rho_fin. destruct H4 as [Hsm4 HK4]. split; [| apply (HJi _ _ _ _ _ HK4)].
  eapply smatchA_entails; [exact Hent | exact Hsm4].
Qed.

Lemma rho_fin_agree : ltac2:(tb__ "0|1|
S10S10S10S0S31Q40A1M0A1S61S3aS21S48R6R5A3S46S7dR1S48A2SdG0S1bR7R2A2S1bR8R2A2A3F_;Fi;G0SdS3S31Q8A1A1S26R7R1A2S26R8R1A2A3Fa;S21S48R9S5bR9R7R5R4R6A5A3F_;F_;F_;Fmd;Fms;Ftp;Frho3;Frho1;Frho0;").
Proof.
  intros rho0 rho1 rho3 tp ms md Hag01 Hrw Hrm. destruct Hag01 as (A & B & Cc).
  unfold rho_fin. split; [|split].
  - intros i Hi. cbn [rw rho_sub set_rl rho_absorb].
    rewrite (wsub_get_id sp NF i Hspid Hi). cbn. rewrite (Hrw i Hi). apply A. exact Hi.
  - intros l. reflexivity.
  - intros a. cbn [rm rho_sub set_rl rho_absorb].
    destruct (in_ranges_dec rho3 [O_b2e] a) as [Hin|Hnin]; [| rewrite Hrm; apply Cc].
    exfalso. destruct Hin as (o & [<-|[]] & Hr). unfold obj_range, obj_lo_of, obj_hi_of, O_b2e in Hr. cbn [ob_base ob_lo ob_hi eval fst snd] in Hr.
    rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Theorem fp_sum_inst : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S69S33Vok;S35S33VJ0;S43R2R1A5S36S33S49U26A1S48R2R1S44A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (runA_tr segs ok FUEL_FP CUTS_FP Pre_ref _ J0 rho tp); [exact HrunW | reflexivity | apply okK_J0 | exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply (triple_pre ok _ _ _ (fun w Hw => W_facts J0 rho1 tp w Hw)). intros HF1.
  eapply triple_conseq with (P := SPA segs (Kf rho1 tp 0) C (rho_wl rho1) tp); [ | intros w Hw; exact Hw |].
  { intros w Hw. apply (reshape rho1 tp rho1 w HF1). destruct Hw as [Hsm HJ]. split; [exact Hsm|]. split; [reflexivity|]. apply Kw0_of_J0. exact HJ. }
  apply (call_soundA segs ok (Kf rho1 tp 0) (Jp rho1 tp) (WLerr.Kw (Jp rho1 tp) MSG_REF [] (length (WLerr.MSG MSG_REF [])))
           (Kf rho1 tp 38) C WLerrS.Pre_wl2 s R WLerr.Posts_wl _ (rho_wl rho1) tp Hefr).
  - exact Hchk.
  - intros rho2 tp2. apply wl_call.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval].
    split; [apply rho_wl_5|]. split; [apply rho_wl_6|]. split; reflexivity.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite HT.
    apply triple_SPA_pure. intros tr md [Et _]. subst tpL.
    apply (triple_SPA_conseq_J segs ok _ (Kf rho1 tp 38)); [intros t md0 (HJ & _ & _); exact HJ|].
    assert (HF' : Forall (holds rho') facts_fp).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rho1) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; apply (sprop_below_mono NF); [unfold NF; lia | exact (proj1 (forallb_forall _ _) fb_facts p Hp)]))).
      exact (proj1 (Forall_forall _ _) (facts_rho_wl rho1 HF1) p Hp). }
    eapply triple_conseq with (P := SPA segs (Kf rho1 tp 38) Tf rho' tp); [ | intros w Hw; exact Hw |].
    { intros w [Hsm HJ]. split; [|exact HJ]. rewrite <- HTf. apply smatchA_add_facts; [exact Hsm | exact HF' | rewrite HnT; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }
    eapply (runA_tr segs ok FUEL_FP CUTS_FP Tf _ (Kf rho1 tp 38) rho' tp); [exact HrunF | exact HlTf | apply Kf_okK | apply Kf_stable |].
    intros L2 rho3 [<-|[]] Hag3. cbn [la_state]. rewrite HnTf in Hag3.
    intros n Hg w [Hsm3 HK3]. destruct w as [tr3 [ms3 md3]].
    pose proof (cleanup (Kf rho1 tp 38) rho rho3 tp tr3 ms3 md3 ltac:(intros r r' t tr' md' HK; exact HK) (conj Hsm3 HK3)) as [HsmP HKP].
    assert (HagF : agree_below NF rho (rho_fin rho rho3 ms3 md3 tp)).
    { apply (rho_fin_agree rho rho1 rho3 tp ms3 md3 Hag1).
      - intros i Hi. destruct Hag3 as (A3 & _ & _). destruct Hag' as (A' & _ & _).
        assert (Hi' : (i < 141)%positive) by (unfold NF in Hi; lia).
        assert (Hi'' : (i < 116)%positive) by (unfold NF in Hi; lia).
        rewrite <- (A3 i Hi'). unfold C in A'. cbn [ax_S ax_setS] in A'. rewrite HnC in A'. rewrite <- (A' i Hi''). reflexivity.
      - intros a. destruct Hag3 as (_ & _ & C3). destruct Hag' as (_ & _ & C'). rewrite <- (C3 a), <- (C' a). reflexivity. }
    apply Hg.
    exists (mkLeafA P_ref RsCut), (rho_fin rho rho3 ms3 md3 tp). split; [left; reflexivity|]. split; [exact HagF|].
    split; [exact HsmP|]. cbn [la_state w_tr w_cfg cfg_model]. destruct HKP as [_ (tr0 & HJ0 & ->)].
    exists tr0. split; [|reflexivity].
    eapply Hst0; [ | apply mat_equiv_refl | exact HJ0].
    eapply agree_below_trans; [apply agree_below_sym; exact Hag1 | exact HagF].
Qed.

Theorem fp_sum_ex_inst : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S68S33S35S33VJ0;S43R2R1A5S36S33S49U26A1S48R2R1S44A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (erunA_tr segs FUEL_FP CUTS_FP Pre_ref _ J0 rho tp); [exact HrunW | reflexivity | exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply (etriple_pre _ _ _ (fun w Hw => W_facts J0 rho1 tp w Hw)). intros HF1.
  eapply etriple_conseq with (P := SPA segs (Kf rho1 tp 0) C (rho_wl rho1) tp); [ | intros w Hw; exact Hw |].
  { intros w Hw. apply (reshape rho1 tp rho1 w HF1). destruct Hw as [Hsm HJ]. split; [exact Hsm|]. split; [reflexivity|]. apply Kw0_of_J0. exact HJ. }
  apply (call_completeA segs (Kf rho1 tp 0) (Jp rho1 tp) (WLerr.Kw (Jp rho1 tp) MSG_REF [] (length (WLerr.MSG MSG_REF [])))
           (Kf rho1 tp 38) C WLerrS.Pre_wl2 s R WLerr.Posts_wl _ (rho_wl rho1) tp Hefr).
  - exact Hchk.
  - intros rho2 tp2. apply wl_call_ex.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval].
    split; [apply rho_wl_5|]. split; [apply rho_wl_6|]. split; reflexivity.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite HT.
    intros w0 [Hsm0 [Et HK0]]. subst tpL. revert w0 Hsm0 HK0.
    assert (HF' : Forall (holds rho') facts_fp).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rho1) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; apply (sprop_below_mono NF); [unfold NF; lia | exact (proj1 (forallb_forall _ _) fb_facts p Hp)]))).
      exact (proj1 (Forall_forall _ _) (facts_rho_wl rho1 HF1) p Hp). }
    assert (HE : etriple segs (SPA segs (Kf rho1 tp 38) Tf rho' tp) (LQA segs (Kwr 38) NF rho tp Posts_ref)).
    { eapply (erunA_tr segs FUEL_FP CUTS_FP Tf _ (Kf rho1 tp 38) rho' tp); [exact HrunF | exact HlTf | apply Kf_stable |].
      intros L2 rho3 [<-|[]] Hag3. cbn [la_state]. rewrite HnTf in Hag3.
      intros w [Hsm3 HK3]. destruct w as [tr3 [ms3 md3]]. exists (tr3, mkCfg ms3 md3). split; [apply wsteps_refl|].
      pose proof (cleanup (Kf rho1 tp 38) rho rho3 tp tr3 ms3 md3 ltac:(intros r r' t tr' md' HK; exact HK) (conj Hsm3 HK3)) as [HsmP HKP].
      assert (HagF : agree_below NF rho (rho_fin rho rho3 ms3 md3 tp)).
      { apply (rho_fin_agree rho rho1 rho3 tp ms3 md3 Hag1).
        - intros i Hi. destruct Hag3 as (A3 & _ & _). destruct Hag' as (A' & _ & _).
          assert (Hi' : (i < 141)%positive) by (unfold NF in Hi; lia).
          assert (Hi'' : (i < 116)%positive) by (unfold NF in Hi; lia).
          rewrite <- (A3 i Hi'). unfold C in A'. cbn [ax_S ax_setS] in A'. rewrite HnC in A'. rewrite <- (A' i Hi''). reflexivity.
        - intros a. destruct Hag3 as (_ & _ & C3). destruct Hag' as (_ & _ & C'). rewrite <- (C3 a), <- (C' a). reflexivity. }
      exists (mkLeafA P_ref RsCut), (rho_fin rho rho3 ms3 md3 tp). split; [left; reflexivity|]. split; [exact HagF|].
      split; [exact HsmP|]. cbn [la_state w_tr w_cfg cfg_model]. destruct HKP as [_ (tr0 & HJ0 & ->)].
      exists tr0. split; [|reflexivity].
      eapply Hst0; [ | apply mat_equiv_refl | exact HJ0].
      eapply agree_below_trans; [apply agree_below_sym; exact Hag1 | exact HagF]. }
    intros w0 Hsm0 HK0. apply HE. split; [| split; [reflexivity | exact HK0]].
    rewrite <- HTf. apply smatchA_add_facts; [exact Hsm0 | exact HF' | rewrite HnT; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
Qed.
End Inst.

Theorem ref_sum : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S69S33Vok;S35S33VJ0;S43R2R1A5S36S33S49U26A1S48R2R1S44A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  destruct shapeW_r as (HnW & HXW & HbW & HfW & _).
  destruct shapeC_r as (Hnl6 & Hrl5 & Ho8 & Hlo & Hhi & Hw8 & Ha8 & Hcb & HswfC & HnC & Hn6 & HnL).
  destruct shapeS_r as (S13 & S15). destruct shapeT_r as (HnT & HlTf & HnTf).
  destruct shapeF_r as (_ & HnF & HbF & HoG1 & HnG1 & HnG2u & HnG3 & HnlG3 & Hspid & HG2o).
  apply (fp_sum_inst W_r S6_r Cs_r O8_r BL_r s_r R_r T_r Tf_r F_r G1_r G2_r G2u_r G3_r sp_r EX_r runW_r HnW HXW HbW HfW splits_r finish_r
           Hnl6 Hrl5 Ho8 Hlo Hhi Hw8 Ha8 Hcb BL_r_val HswfC HnC Hn6 HnL efr_r chk_r S13 S15 T_r_eq HnT Tf_r_eq HlTf HnTf runF_r HbF
           xp1_r HoG1 HnG1 drop1_r HG2o unlist_r HnG2u ltac:(rewrite <- unlist_r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) xp2_r HnG3 HnlG3 ent_r Hspid).
Qed.

Theorem ref_sum_ex : ltac2:(tb__ "0|0|
S10S0S31Q40A1A1S68S33S35S33VJ0;S43R2R1A5S36S33S49U26A1S48R2R1S44A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  destruct shapeW_r as (HnW & HXW & HbW & HfW & _).
  destruct shapeC_r as (Hnl6 & Hrl5 & Ho8 & Hlo & Hhi & Hw8 & Ha8 & Hcb & HswfC & HnC & Hn6 & HnL).
  destruct shapeS_r as (S13 & S15). destruct shapeT_r as (HnT & HlTf & HnTf).
  destruct shapeF_r as (_ & HnF & HbF & HoG1 & HnG1 & HnG2u & HnG3 & HnlG3 & Hspid & HG2o).
  apply (fp_sum_ex_inst W_r S6_r Cs_r O8_r BL_r s_r R_r T_r Tf_r F_r G1_r G2_r G2u_r G3_r sp_r EX_r runW_r HnW HXW HbW HfW splits_r finish_r
           Hnl6 Hrl5 Ho8 Hlo Hhi Hw8 Ha8 Hcb BL_r_val HswfC HnC Hn6 HnL efr_r chk_r S13 S15 T_r_eq HnT Tf_r_eq HlTf HnTf runF_r HbF
           xp1_r HoG1 HnG1 drop1_r HG2o unlist_r HnG2u ltac:(rewrite <- unlist_r; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) xp2_r HnG3 HnlG3 ent_r Hspid).
Qed.
End Fp.
End DrvFp.

(* [comment removed for export] *)
Module Icpt_memchr_st.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "nat"; "bool"; "option"; "Some"; "list"; "false"; "app"; "pair"; "prod"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "SVar"; "SAlu"; "sv"; "ss_next"; "sobj"; "cell"; "mkObj"; "SPEq"; "ss_lenient"; "DImage"; "SPAlign"; "FcsrFrm0"; "SPBranch"; "mkSS"; "sprop_below"; "sstate"; "swf"; "DList"; "DUnknown"; "mkCell"; "sprop_eqb"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "sym_runA"; "mkLeafA"; "la_state"; "axwf"; "entailsA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GEU"; "BC_LTU"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "vXB"; "vXL"; "CUTS_MCI"; "FUEL_MCI"; "sX"; "facts_mci"; "E_call"; "E_ripS"; "P_mci"; "Pre_mci"; "vXL8"; "vXO"; "N1"; "s_call"; "D_MCI"; "E_rip"; "G_B"; "G_S"; "R_B"; "R_S"; "R_call"; "R_rip"; "T_B"; "T_S"; "T_rip"; "T_ripF"; "s_rip"; "ENDA"; "T_imp"; "X_mci"; "mci_ret"; "objs_mci"; "sp_B"; "sp_S"; "GEU65"; "O_realmc"; "O_strS"; "O_win"; "XB"; "XS"; "big_facts"; "factsB"; "factsS"; "mci_entry"; "post_facts"; "rip8_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "two62"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXMerge"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "RsFuel"; "RsSymJump"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "opp"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA"; "Pre_memchr0"; "P_ret"; "Posts_memchr0"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "HSE"; "O_rtc2"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA.MCHAddr"; "memchr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition mci_entry : Z := 0x4ea8c.
Definition mci_ret : Z := 0x4eb6c.

Definition O_realmc : sobj := ltac2:(tb__ "0|0|
S16SeZ0A1SeZe6638A1SeZe6640A1S2S15A1S19A5").
Definition O_realsn : sobj := ltac2:(tb__ "0|0|
S16SeZ0A1SeZe6728A1SeZe6730A1S2S15A1S19A5").
Definition O_cfsl : sobj := ltac2:(tb__ "0|1|
S16SeZ0A1SeZ17fce0A1M0SeZ17fce8A1S0S15S23G0Z8SeZ101010101010101A1A3S2S15A1A3S19A5").
Definition D_MCI : Z := 2208.
Definition O_win : sobj := ltac2:(tb__ "0|0|
S16S10PaA1SeS76S43A1A1SeZ0A1S2S15A1S22A5").
Definition vXB := SVar 18. Definition vXL := SVar 19. Definition vXO := SVar 20.
Definition sX : sv := SAlu ALU_ADD vXB vXO.
Definition O_strS : sobj := ltac2:(tb__ "0|0|
S16S39SeZ0A1S10P11A1S2S15A1S21P3A1A5").
Definition facts_mci : list sprop := ltac2:(tb__ "0|d|
S0SdS1cS32S10P10A1M0S10PeA1M1A3S0SdSfS11S30G0SeZ8A1M2A3S10P11A1M3A2S0SdSfG2G3A2S0SdSfG3SeS6cA1M4A2S0SdSfG1G4A2S0SdSfSeZ1A1M5S39A2S0SdSfS39G4A2S0SdS1aPaM6Z4A2S0SdSfSeS78S65Z1000A2A1S10G6A1M7A2S0SdSfG7SeS75Z2M8Z2fA2M9A1MaA2S0SdSfS11S30S40G3A3S36A2S0SdSfS40S36A2S0SdSfG3S36A2S0SdSfS36SeS75G8Z28A2A1A2S0SdSfSeS88A1S35A2S0SdSfS11S30S35S36A3MbGaA2S0SdSfS35SeS77G9Z40A2A1A2S0SdS1aP12Z6McA2S0SdS1aP13GcA2S0SdSfS11S30S39G5A3GbA2S0SdSfS11S30G0SeZ10A1A3G3A2S2SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X_mci : list (sv * sv) := ltac2:(tb__ "0|1|
S0SbS12S12A2M0SaS12S12S35S36A4S0G0SaS12S12S11S30S10PaA1SeS76S43A1A1A3SeS43A1A4S2G0A1A3A3").
Definition objs_mci : list sobj := ltac2:(tb__ "0|0|
S9S14S0S14S5aS0S14S59S0S14S87S0S14S89S0S14S58S2S14A1A3A3A3A3A3S66A3").
Definition Pre_mci : axst := ltac2:(tb__ "0|1|
S64S1dS60S69S6bS0SbS3S12A2M0SaS3S12UaS39A4S0G0SaS3S12UbSeZ0A1A4S2G0A1A3A3A2S68S1bScS12A1S54S3aS67S8A9S52A2").
Definition CUTS_MCI : ltac2:(tb__ "0|0|
S7S34A1") := ltac2:(tb__ "0|0|
S0S34S8dS0S34S8bS0S34S53S2S34A1A3A3A3").
Definition FUEL_MCI : nat := 400%nat.
Definition lf0 (S : axst) (r : option (list leafA)) (i : nat) : axst := ltac2:(tb__ "0|1|
S5S7S28A1M0A1S2aLr;Vr;G0S2dS81S28Vi;R1S2cVS;S73A2A4A1Lls;VS;X5x2").

Definition run_call__R : option (list leafA) := ltac2:(tb__ "0|0|
S2bS63S38S37S3eS1A5").
Local Strategy expand [run_call__R].
Definition E_call : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => lf0 Pre_mci (ro1__) 0) run_call__R).
Definition s_call : wsub := Eval vm_compute in infer_sub 10 (ax_S E_call) (ax_S Pre_memchr0).
Definition R_call : list sobj := Eval vm_compute in match entails_frA E_call Pre_memchr0 s_call with Some R => R | None => [] end.
Definition T_imp : axst := Eval vm_compute in import_postA s_call Pre_memchr0 P_ret E_call R_call.
Definition T_impF : axst := ax_add_facts facts_mci T_imp.

Definition ENDA : sv := ltac2:(tb__ "0|0|
S11S30S11S30S39S11S30S10P8cA1SeZ1A1A3A3SeN1A1A3").
Definition post_facts : list sprop := ltac2:(tb__ "0|0|
S0SdSfS35S50A2S0SdSfS11S30S50SeZ1A1A3S11S30S35S36A3A2S2SdA1A3A3").
Definition GEU65 : sprop := ltac2:(tb__ "0|0|
S1cS31SeZffffffffffffffbfA1S11S30S10P8cA1SeN40A1A3A3").
Definition factsS : list sprop := SPNot GEU65 :: post_facts.

Definition vXL8 : sv := SAlu ALU_ADD vXL (SLit (-8)).
Definition rip8_facts (n : sv) : list sprop := ltac2:(tb__ "0|3|
S0SdSfS11S30S40Vn;A3S3fA2S0SdSfS40S3fA2S0SdSfVn;S3fA2S0SdSfS3fSeS75Z2M0Z28A2A1A2S0SdSfS11S30S35S3fA3M1SeS77S75G0Z2fA2Z8A2A1M2A2S0SdSfS35G2A2S0SdSfS35G1A2S0SdSfG1S11S30S35S36A3A2S2SdA1A3A3A3A3A3A3A3A3").
Definition N1 : sv := SAlu ALU_ADD (SVar 140) (SLit 1).
Definition big_facts : list sprop := ltac2:(tb__ "0|0|
S9SdS0SdSfS11S30S40S41A3S36A2S0SdSfS41S36A2S0SdSfSeZ1A1S41A2S2SdA1A3A3A3S62S41A1A3").
Definition factsB : list sprop := ltac2:(tb__ "0|0|
S0SdS57S9SdS61S5dA3A3").
Definition T_S : axst := ax_add_facts factsS T_impF.
Definition T_B : axst := ax_add_facts factsB T_impF.

Definition run_S__R : option (list leafA) := ltac2:(tb__ "0|0|
S2bS63S38S37S4cS1A5").
Local Strategy expand [run_S__R].
Definition R_S : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => lf0 T_S (ro2__) 0) run_S__R).

Definition run_B__R : option (list leafA) := ltac2:(tb__ "0|0|
S2bS63S38S37S4bS1A5").
Local Strategy expand [run_B__R].
Definition E_rip : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => lf0 T_B (ro3__) 0) run_B__R).
Definition E_ripS : axst := Eval vm_compute in match split_obj_at (ax_S E_rip) 1 (SLit (-2128)) with Some S' => ax_setS E_rip S' | None => E_rip end.
Definition s_rip : wsub := Eval vm_compute in ((16%positive, vXL8) :: infer_sub 10 (ax_S E_ripS) (ax_S Pre_rip)).
Definition R_rip : list sobj := Eval vm_compute in match entails_frA E_ripS Pre_rip s_rip with Some R => R | None => [] end.
Definition T_rip : axst := Eval vm_compute in import_postA s_rip Pre_rip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.P_ret E_ripS R_rip.
Definition T_ripF : axst := ltac2:(tb__ "0|0|
S8fS0SdS17S10P8cA1S10P10A1A2S3aA3S4dA2").
Definition run_B2__R : option (list leafA) := ltac2:(tb__ "0|0|
S2bS63S38S37S4eS1A5").
Local Strategy expand [run_B2__R].
Definition R_B : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => lf0 T_ripF (ro4__) 0) run_B2__R).

Definition XS : list axform := ltac2:(tb__ "0|0|
S0S6dS6eS0S3U1S0S3U0S0S3U2S0S3U3S0S3U4S0S3U5S0S3U6S2S3A1A3A3A3A3A3A3A3A1S2S6dA1A3").
Definition XB : list axform := ltac2:(tb__ "0|1|
S0S6dS71U0M0A1S0S6dS6eS0S3G0S0S3U5S0S3U4S0S3U6S0S3U1S0S3U7S0S3U2S0S3U3S2S3A1A3A3A3A3A3A3A3A3A1S0S6dS70G0A1S2S6dA1A3A3A3").
Definition G_S : axst := Eval vm_compute in match apply_axforms R_S XS with Some A => A | None => R_S end.
Definition G_B : axst := Eval vm_compute in match apply_axforms R_B XB with Some A => A | None => R_B end.
Definition P_mci0 : axst := ltac2:(tb__ "0|1|
S64S1dS53S69S6aS67A1S0SbS3S12A2M0SaS3S12UaS11S30S39S10P8cA1A3A4S2G0A1A3A2S68S1bScS12A1S54S3aP8dS8A9S52A2").
Definition F_post : list sprop := ltac2:(tb__ "0|0|
S0SdS17S10P8cA1S10P10A1A2S2SdA1A3").
Definition P_mci : axst := ax_add_facts F_post P_mci0.
Definition Posts_mci : list leafA := ltac2:(tb__ "0|0|
S0S28S2cS3dS74A2S2S28A1A3").
Definition sp_S : wsub := Eval vm_compute in infer_sub NF (ax_S G_S) (ax_S P_mci0).
Definition sp_B : wsub := Eval vm_compute in infer_sub NF (ax_S G_B) (ax_S P_mci0).

Lemma mci_wf : ltac2:(tb__ "0|0|
S27S26S4S2eS3eA1S1A3S27S26S4S20S29S3eA1A1S1A3S27S26S4S2eS3dA1S1A3S26S4S20S29S3dA1A1S1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma run_call : ltac2:(tb__ "0|1|
S26S5S7S28A1M0A1S2bS63S38S37S3eS1A5S6G0S0S28S2cS3bS72A2S2S28A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_call__R <: run_call__R = Some [mkLeafA E_call RsCut]). Qed.
Lemma efr_call : ltac2:(tb__ "0|1|
S26S5S7S14A1M0A1S85S3bS7aS42A3S6G0S49A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_call : ltac2:(tb__ "0|0|
S26S4S84S3bS7aS42S49S80S28S2aS2dS7cA4A5S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_call : ltac2:(tb__ "0|0|
S26S2aS86S42S7aS7bS3bS49A5S51A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run_S : ltac2:(tb__ "0|1|
S26S5S7S28A1M0A1S2bS63S38S37S4cS1A5S6G0S0S28S2cS48S72A2S2S28A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_S__R <: run_S__R = Some [mkLeafA R_S RsCut]). Qed.
Lemma run_B : ltac2:(tb__ "0|1|
S26S5S7S28A1M0A1S2bS63S38S37S4bS1A5S6G0S0S28S2cS44S72A2S2S28A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_B__R <: run_B__R = Some [mkLeafA E_rip RsCut]). Qed.
Lemma split_rip : ltac2:(tb__ "0|0|
S26S5S1fA1S8eS29S44A1U1SeN850A1A3S6S1fS29S3cA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma efr_rip : ltac2:(tb__ "0|1|
S26S5S7S14A1M0A1S85S3cS79S4fA3S6G0S4aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_rip : ltac2:(tb__ "0|0|
S26S4S84S3cS79S4fS4aS80S28S2aS2dS8cA4A5S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_rip : ltac2:(tb__ "0|0|
S26S2aS86S4fS79S8aS3cS4aA5S4dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run_B2 : ltac2:(tb__ "0|1|
S26S5S7S28A1M0A1S2bS63S38S37S4eS1A5S6G0S0S28S2cS47S72A2S2S28A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_B2__R <: run_B2__R = Some [mkLeafA R_B RsCut]). Qed.
Lemma xf_S : ltac2:(tb__ "0|0|
S26S5S2aA1S6fS48S5cA2S6S2aS46A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma xf_B : ltac2:(tb__ "0|0|
S26S5S2aA1S6fS47S5bA2S6S2aS45A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_S : ltac2:(tb__ "0|0|
S26S4S2fS46S3dS56A3S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_B : ltac2:(tb__ "0|0|
S26S4S2fS45S3dS55A3S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_mci : ltac2:(tb__ "0|0|
S27S26S4S82S56S67A2S1A3S26S4S82S55S67A2S1A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma shape_call : ltac2:(tb__ "0|2|
S27S26S33S13S29S3bA1A1S67A3S27S26S4S18S29S3eA1M0A1S8A3S27S26S33S13G0A1S67A3S26S12S83S42P10M1A2S10G1A1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shape_imp : ltac2:(tb__ "0|5|
S27S26S33S13S29S51A1M0A1P8dM1A3S27S26S4S18S29S4cA1M2A1S8A3S27S26S33S13G2A1G1A3S27S26S4S18S29S4bA1M3A1S8A3S27S26S33S13G3A1G1A3S27S26S4S7eSdS24S17S10P8cA1S10P10A1A2A1S25G0A1A3S1A3S27S26S4S7dSdS1eG1A1M4S9SdS5fS3aA3A3S1A3S26S4S7dSdG4S9SdS5eS3aA3A3S1A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shape_rip : ltac2:(tb__ "0|3|
S27S26S33S13S29S3cA1A1S13S29S44A1A1M0A3S27S26S33S13S29S4dA1A1Pb5M1A3S27S26S4S18S29S4eA1M2A1S8A3S27S26S33S13G2A1G1A3S27S26S4S7fP8dG0A2S1A3S26S4S7dSdS1eG1A1S0SdS17S10P8cA1S10P10A1A2S3aA3A3S1A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shape_ret : ltac2:(tb__ "0|2|
S27S26S33S13S29S48A1A1M0S13S29S46A1A1A3S27S26S33S13S29S47A1A1M1S13S29S45A1A1A3S27S26S4S7fP8dG0A2S1A3S26S4S7fPb5G1A2S1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Icpt_memchr_st.

(* [comment removed for export] *)
Module Start5bStates.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "Some"; "option"; "list"; "bool"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "mkLeafA"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "SLit"; "SVar"; "SPUle"; "ss_objs"; "sprop_eqb"; "SPAlign"; "ss_next"; "ss_pc"; "SAlu"; "SPEq"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "SPIN_MMAPORDIE"; "ECALL_MMAP"; "fail_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Start5bStates"; "E_s14"; "E_s15"; "E_s15u"; "ECALL_MUNMAP"; "SPIN13"; "SPIN14"; "S_s13ok"; "S_s14ok"; "F13"; "F14"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "ALU_SLL"; "@Stdlib.Lists.List"; "existsb"; "last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Start5CallStates"; "E_s13g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "axA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "mmap_obj"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Start5CallStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ECALL_MUNMAP : Z := 0x706ac.

Definition F13 : list sprop := ltac2:(tb__ "0|3|
S0S13S1aP4dM0ZcA2S0S13S17S15Z1000M1A1S16G0A1M2A2S0S13S17G2S15S39Z7fffff800000G1A2A1A2S1S13A1A3A3A3").
Definition S_s13ok : axst := ltac2:(tb__ "0|2|
S36S3bS2eS37SdS35A1M0S16P4dM1A1S7S14S18G0A1S0S14S38G1Z1000A2S1S14A1A3A3P4eA4A2A1").
Definition run13_ok__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS12Ubb8S0S8S21S1S8A1A3S2cS2A5").
Local Strategy expand [run13_ok__R].
Definition E_s14 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 S_s13ok (ro1__)))) run13_ok__R).
Definition run13_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS12Uc8S0S8S20S1S8A1A3S22S35A1S2A5").
Local Strategy expand [run13_fail__R].
Definition SPIN13 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 (fail_state E_s13g) (ro2__)))) run13_fail__R).
Lemma run13_ok : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12Ubb8S0S8S21S1S8A1A3S2cS2A5S3G0S0ScSfS26S23A2S1ScA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run13_ok__R <: run13_ok__R = Some [mkLeafA E_s14 RsCut]). Qed.
Lemma run13_fail : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12Uc8S0S8S20S1S8A1A3S22S35A1S2A5S3G0S0ScSfS2aS23A2S1ScA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run13_fail__R <: run13_fail__R = Some [mkLeafA SPIN13 RsCut]). Qed.
Lemma spin13 : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12U2S0S8S20S1S8A1A3S2aS2A5S3G0S0ScSfS2aS23A2S1ScA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_s14_at : ltac2:(tb__ "0|2|
SbSaS8S1cSdS26A1M0A1M1S21A3SbSaS9S1bG0A1P4eA3SaS4S30A1S24S12G1A2S3S30S31A2A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F14 : list sprop := ltac2:(tb__ "0|3|
S0S13S1aP4eM0ZcA2S0S13S17S15Z1000M1A1S16G0A1M2A2S0S13S17G2S15S39Z7fffff800000G1A2A1A2S1S13A1A3A3A3").
Definition S_s14ok : axst := ltac2:(tb__ "0|2|
S36S3bS2fS37SdS26A1M0S16P4eM1A1S7S14S18G0A1S0S14S38G1Z1000A2S1S14A1A3A3P4fA4A2A1").
Definition run14_ok__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS12Ubb8S0S8S29S0S8S21S1S8A1A3A3S2dS2A5").
Local Strategy expand [run14_ok__R].
Definition E_s15 : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => ((leaf1 S_s14ok (ro3__)))) run14_ok__R).
Definition run14_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS12Uc8S0S8S20S1S8A1A3S22S26A1S2A5").
Local Strategy expand [run14_fail__R].
Definition SPIN14 : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => ((leaf1 (fail_state E_s14) (ro4__)))) run14_fail__R).
Lemma run14_ok : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12Ubb8S0S8S29S0S8S21S1S8A1A3A3S2dS2A5S3G0S0ScSfS27S23A2S1ScA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run14_ok__R <: run14_ok__R = Some [mkLeafA E_s15 RsCut]). Qed.
Lemma run14_fail : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12Uc8S0S8S20S1S8A1A3S22S26A1S2A5S3G0S0ScSfS2bS23A2S1ScA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run14_fail__R <: run14_fail__R = Some [mkLeafA SPIN14 RsCut]). Qed.
Lemma spin14 : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12U2S0S8S20S1S8A1A3S2bS2A5S3G0S0ScSfS2bS23A2S1ScA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_s15_at : ltac2:(tb__ "0|2|
SbSaS8S1cSdS27A1M0A1M1S29A3SbSaS9S1bG0A1P4fA3SaS4S30A1S24S12G1A2S3S30S31A2A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_s15u : axst := Eval vm_compute in (drop_last_obj E_s15).
Lemma E_s15_split : ltac2:(tb__ "0|1|
SaS5S14A1S18SdS27A1A1M0S7S14S18SdS28A1A1S0S14S34S14G0S38P4eZ1000A2A3S1S14A1A3A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_s15u_eq : ltac2:(tb__ "0|0|
SaS11S10S27S25SdS27A1S18SdS28A1A1A2A2S28A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition S_s15ok : axst := ltac2:(tb__ "0|1|
S36S37SdS28A1M0S15Z0A1S18G0A1P4fA4A1").
Lemma E_s15u_facts : ltac2:(tb__ "0|3|
SbSaS6S33S13S19S17S16P1M0A1S15Z7fffffffff20A1A2A1S1fSdS28A1A1M1A3S2A3SbSaS6S33S13S19S1eS1dS32S16P23A1M2S15Z3A1A3S16P22A1A2A1G1A3S2A3SbSaS6S33S13S19S17G2S15S39S3aZ2Z3dA2Z1A2A1A2A1G1A3S2A3SaS6S33S13S19S1aG0Z4A2A1G1A3S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start5bStates.

