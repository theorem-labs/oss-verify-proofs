(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ListCommitA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh Musl_wl_err Asan_memcpy_contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_finalize Lib_builderH_defs.

(* [comment removed for export] *)
Module Fps_pre.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "list"; "nil"; "pair"; "prod"; "option"; "bool"; "true"; "None"; "app"; "Some"; "andb"; "false"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "sobj"; "SVar"; "SAlu"; "sstate"; "ss_next"; "SPAlign"; "cell"; "ob_base"; "ss_objs"; "ss_regs"; "SPEq"; "mkObj"; "mkSS"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "ss_lenient"; "ss_pc"; "DUnknown"; "FcsrFrm0"; "c_off"; "sprop_below"; "sprop_eqb"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "sv_eqb"; "tfact"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "BASEF"; "D_FPS"; "facts_fps"; "FQC"; "CUTS_FPS"; "FQB"; "FUEL_T"; "O_fwin"; "TPL"; "X_fps"; "drop_cellsF"; "facts_in"; "keep_cell"; "mc_entry"; "mc_musl"; "mc_ret"; "objs_fps"; "prune0"; "regs_fps"; "setF"; "set_facts"; "sp_off"; "str_facts"; "vfp_entry"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "ALU_ADD"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "sX"; "vXL"; "vXB"; "vXO"; "O_cfsl"; "O_realmc"; "O_realsn"; "O_strS"; "factsB"; "factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "ax_setS"; "la_reason"; "la_state"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXMerge"; "AXRebase"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "opp"; "leb"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "ms16"; "O_cflag"; "O_realm"; "O_realv"; "O_rtc2"; "O_ssp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "two62"; "NF"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "mkA"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface"; "fp_entry"; "fp_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface"; "FERR"; "O_ferr0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "HSE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st"; "si_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen.ISLAddr"; "isl_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "replace_obj_at"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymBytes SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform ListCommitA DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Musl_wl_err.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition FMT_COPEN : Z := 0x1ee60.
Definition FMT_RDERR : Z := 0x1ee75.
Definition FMT_USAGE : Z := 0x160bc.
Definition TPL : Z := 0x621278.
Definition D_FPS : Z := 1024 + D_SI.
Definition O_fwin : sobj := ltac2:(tb__ "0|0|
S1fS15PaA1S12S6aS37A1A1S12Z0A1S3S1aA1S28A5").
Definition str_facts : list sprop := ltac2:(tb__ "0|9|
S0S11S13S16S4fS15P10A1M0S12Z8A1M1A3S15P11A1M2A2S0S11S13G1G2A2S0S11S13G2S12S77A1M3A2S0S11S13S12Z1A1M4S51A2S0S11S13S51G3A2S0S11S13S16S4fS54G2A3S52A2S0S11S13S54S52A2S0S11S13G2S52A2S0S11S13S52S12S68Z2M5Z28A2A1A2S0S11S13S12S84A1S53A2S0S11S13S16S4fS53S52A3M6S12S68G5Z2fA2M7A1A2S0S11S13S53S12S69G7Z40A2A1A2S0S11S19P12Z6M8A2S0S11S19P13G8A2S0S11S13S16S4fS51G4A3G6A2S0S11S13G0S12Z1ffffA1A2S0S11S13S15PaA1S51A2S0S11S13S16S4fG0S12Z10A1A3G2A2S3S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition facts_fps : list sprop := ltac2:(tb__ "0|2|
SaS11S0S11S19PaM0Z4A2S0S11S13S12Z7fff7ffff000A1S15G0A1M1A2S0S11S13G1S12S69S68Z2Z2fA2Z10A2A1A2S0S11S71Z918A1S3S11A1A3A3A3A3S4cA3").
Definition X_fps (fblk flen : Z) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5S10S10A2M0S4S10S10S12Vfblk;A1S12Vflen;A1A4S0G0S4S10S10S53S52A4S0G0S4S10S10S16S4fS15PaA1S12S6aS37A1A1A3S12S37A1A4S3G0A1A3A3A3").
Definition objs_fps : list sobj := ltac2:(tb__ "0|0|
SaS14S0S14S3dS0S14S58S0S14S82S0S14S83S0S14S75S0S14S72S0S14S74S0S14S73S0S14S56S0S14S57S0S14S55S0S14S76S3S14A1A3A3A3A3A3A3A3A3A3A3A3A3S7cA3").
Definition regs_fps (fmt : Z) : list sv := ltac2:(tb__ "0|1|
S7bS7aS0S5S1S10A2M0S4S1S10U3S12Z10800A1A4S0G0S4S1S10U4S12S3eA1A4S0G0S4S1S10UaS12S81A1A4S0G0S4S1S10UbS12Vfmt;A1A4S0G0S4S1S10UcS51A4S3G0A1A3A3A3A3A3A2").
Definition Pre_fps (fmt fblk flen : Z) : axst := ltac2:(tb__ "0|0|
S7dS20S7fS48Vfmt;A1S79S29S9S10A1S46S38S78SdA9S3fVfblk;Vflen;A2A2").
Definition Pre_co : axst := Pre_fps FMT_COPEN 0x1ee40 0x80.

Definition mc_entry : Z := 0x5d86c.
Definition mc_musl : Z := 0xdac00.
Definition mc_ret : Z := 0x5d99c.
Definition vfp_entry : Z := 0xd743c.
Definition CUTS_FPS : list Z := ltac2:(tb__ "0|0|
S0S33S87S0S33S86S0S33S85S0S33S4dS0S33S43S0S33S44S0S33S45S0S33Zd6760S0S33S80S3S33A1A3A3A3A3A3A3A3A3A3").

Definition setF (S : sstate) (F : list sprop) : sstate := ltac2:(tb__ "0|0|
S20S27VS;A1S1dVS;A1S2fVS;A1S2eVS;A1S30VS;A1S1cVS;A1VF;S18VS;A1S26VS;A1A9").
Definition set_facts (A : axst) (F : list sprop) : axst := ltac2:(tb__ "0|0|
S5eVA;S49S5bVA;A1VF;A2A2").
Definition keep_cell (lo : Z) (c : cell) : bool := ltac2:(tb__ "0|3|
S10S7Lx;S2aVc;A1S33S6bVlo;R1A2Lo;S34S8Li;S4eS10S10S8Lb;La;M0Lop;M1G1S50G0Lop;M2G2S7S35S10S8La;Lw;Lsgn;S34S10S33S8Lk;Li;Ll;X10x8").
Definition drop_cellsF (keep : cell -> bool) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1fS1bVo;A1S24Vo;A1S23Vo;A1S6eS1aVkeep;S21Vo;A1A3S22Vo;A1A5").

Definition sp_off (S : sstate) (b : sv) : option Z := ltac2:(tb__ "0|a|
S10S6S33A1M0Lx;S70S10U2S1dVS;A1S12Z0A1A4S33S9S33A1M1Lz;S34G1Li;M2S4eS10S10S4eG0Lop;R3S10G0Lb0;R1S33S7G0L_;S31R3Vb;A2SbS33R1A2G1X7x2Lo;G2S4eS10S10G1Lb1;La;M3Lop0;M4G4S50G3Lop0;M5G5S7S35S10G1La;Lw;Lsgn;M6S34S10S33G1Lk;Li;Ll;M7X10x8G1G1G1G1G1G1G1G1G1X4exaLb0;Le;Lop;S4eS10S10G1Lb0;La;M8Lop;S50G8Lop;M9G9G6G7X10x8").
Definition prune0 (S : sstate) : option sstate := ltac2:(tb__ "0|4|
S2S14A1M0S6S17A1M1Lx;S1cVS;A1S9S17A1M2S14G0S25G1Lx;S22R2A1S6S33A1G1Lx;S4bVS;S1bR2A1A2S33S89VS;U0S40S42R1A1R3A2A3S17S7G1L_;S88VS;R1A2SbS17R1A2G2X7x2TT;Llo;G2X6x2G2G2S34G2Ll;M3G3S33S10S2S5S33S33A2A1S2S32A1G2Ltmpl;Lflds;Lcnt;Lesz;X25x6Ll;Lo;X2x2").
Definition trim (F : list sprop) (A : axst) : axst := ltac2:(tb__ "0|0|
S4aVA;VF;A2S5dS6S17A1S5dLx;S47S5bR1A1A1S17S5eR2R1A2LT;R1X6x2TA1;").

Definition facts_in (F : list sprop) (S : sstate) : bool := ltac2:(tb__ "0|0|
S6cS11S11S6dS11S2cR1A1S2dVS;A1A3Lf;VF;A3").
Definition FUEL_T : nat := 4000%nat.

Definition seg0 (A : axst) : option axst := ltac2:(tb__ "0|5|
S6S2S5cA1M0A1S6S5dA1M1Lx;S61S7eS3cS3aVA;S8A5G0G0G1Ll;R1S9S5dA1M2S5cG0G0G1Ll0;R1S67G1Lx;S5fR2A1G2S7G1L_;ScS8aS18S5bVA;A1A1S18S5bS60R2A1M3A1M4A1A2SfS26G4A1A1A2SbS5dG3A2G2X7x2G2G2G2G2G2X67x7S5cG0G2Ll2;Ll1;X2x2Ll0;LL;X2x2Ll;G2X6x2").

Fixpoint runp (Fs : list (list sprop)) (A : axst) : option axst :=
  match Fs with
  | [] => Some A
  | F :: Fs' => match seg0 (trim F A) with Some B => runp Fs' B | None => None end
  end.

Definition fs_ok (Fs : list (list sprop)) (S : sstate) : bool := ltac2:(tb__ "0|1|
S6cS2S11A1M0G0ScS41R1VS;A2S6cS11S2bS18VS;A1A1R1A3A2LF;VFs;A3").

Definition BASEF : list sprop := ltac2:(tb__ "0|2|
S0S11S19PaM0Z4A2S0S11S13S12Z7fff7ffff000A1S15G0A1M1A2S0S11S13G1S12S69S68Z2Z2fA2Z10A2A1A2S0S11S71Z918A1S3S11A1A3A3A3A3").

Definition FQC : list sprop := ltac2:(tb__ "0|0|
S0S11S1eS15P8cA1S15P10A1A2SaS11S5aS38A3A3").
Definition FQB : list sprop := ltac2:(tb__ "0|0|
S0S11S1eS15P8cA1S15P10A1A2SaS11S59S38A3A3").
Definition STRP : list sprop := ltac2:(tb__ "0|0|
S0S11S13S12Z1A1S51A2S0S11S13S51S12S77A1A2S3S11A1A3A3").

Definition FSS : list (list sprop) := ltac2:(tb__ "0|1|
S0S2S11A1M0S39S0G0S36S0G0S36S0G0S36S0G0S36S0G0S36S0G0S36S0G0S39S3G0A1A3A3A3A3A3A3A3A3").
Definition FSB : list (list sprop) := ltac2:(tb__ "0|1|
S0S2S11A1M0S36S0G0S36S0G0S36S0G0S36S0G0S36S0G0S36S0G0S36S0G0S3bS3G0A1A3A3A3A3A3A3A3A3").
Definition sho (A : axst) : ltac2:(tb__ "0|0|
S2S5S5S5S10S10A2S10A2S1A2A1") := ltac2:(tb__ "0|2|
S6fS14S5S5S5S10S10A2M0S10A2M1S1A2S14S4G1S1S4G0S10S4S10S10S1bR1A1S24R1A1A4S23R1A1A4SeS1aS21R1A1A2A4Lo;S1cS5bVA;A1A1A4").
Definition shl (r : option (list leafA)) : ltac2:(tb__ "0|0|
S2S5S5S33S67A2S34A2A1") := ltac2:(tb__ "0|4|
S6S2S5cA1M0A1S2S5S5S33S67A2M1S34A2M2A1Lr;Vr;G0S6fS5cG2S5cS4G1S34S4S33S67S27S5bS60R1A1A1M3A1S5fR1A1A4S18G3A1A4Ll;R1A4Lls;S3G2A1X6x2").

Definition XF6 : list axform := ltac2:(tb__ "0|11|
S0S62S65U0M0A1S0S62S63S0S1U5M1S0S1G0S0S1U6M2S0S1U4M3S0S1U7M4S0S1U8M5S0S1U1M6S0S1U9M7S0S1UaM8S0S1UbM9S0S1UcMaS0S1UdMbS0S1UeMcS0S1UfS0S1U2MdS0S1U3MeS3S1A1MfA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S62S64G0A1M10S0S62G10S0S62S66G0S12N400A1A2S0S62S63S0S1GdS0S1G0S0S1G6S0S1GeS0S1G3S0S1G1S0S1G2S0S1G4S0S1G5S0S1G7S0S1G8S0S1G9S0S1GaS0S1GbS0S1GcGfA3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S3S62A1A3A3A3A3A3A3").

Definition zvar (T : axst) : positive := ltac2:(tb__ "0|4|
S10S34Lx;S70S10UaS1dS5bVT;A1A1S12Z0A1A4S33P1M0Lz;S34R1Lv;S4eS10S10G0Lb;La;M1Lop;M2G2S50G1Lop;M3G3S7S35S10G0La;Lw;Lsgn;S34S10S33G0Lk;Li;Ll;X10x8").
End Fps_pre.

(* [comment removed for export] *)
Module Str_strnlenA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "agree_below"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA"; "FirstNul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st"; "Posts_sn"; "Pre_sn"; "P_sn"; "s_call"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Icpt_memchr"; "Jf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "entailsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform StrBytes MuslWL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Icpt_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Section SN.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Hypothesis Hok : ok_frameA segs ok J0.
Hypothesis Hst0 : stableA segs NF J0.

Lemma FirstNul_call_sn : ltac2:(tb__ "0|0|
S1S5S3A1S11S8R3A1S8S17S16R4R3R2A3ScA2A1F_;Fms;FR;Frho;").
Proof.
  intros rho R ms [H0 H1]. destruct sn_shape as (_ & _ & _ & _ & S16 & _). unfold FirstNul.
  change (rw (rho_sub (rho_absorb rho R ms) s_call) 16) with (eval (rho_absorb rho R ms) (wsub_get s_call 16)). rewrite S16.
  cbn [eval rw rl rho_sub rho_absorb]. split; assumption.
Qed.

Lemma to_post_sn : ltac2:(tb__ "0|0|
S1aS18S1S1S5SfQ40A1A1S1S15S10S6S1bR7SbR6A3S7A3S10S6S19R7S4A2S7A3S2S4R7R6A3S2S4R7R5A3SeS0S12VJ0;R8R7A3RbR6R7R5A6SdS0VJ0;S4RaR8S9R6A7F_;F_;F_;F_;F_;Fw;FrhoR;Ftp;Frho1;Frho;Fsp;FG;").
Proof.
  intros G sp rho rho1 tp rhoR w Hent Hid Hag1 HagR HS.
  pose proof (SPA_entails segs (Jf J0 rho1 tp) NF G P_sn sp rhoR tp w Hent Hid (Jf_stable J0 Hst0 rho1 tp NF (Pos.le_refl _)) HS) as [Hsm (Hag & _ & HJ)].
  exists (mkLeafA P_sn RsSymJump), (rho_sub rhoR sp). split; [left; reflexivity|]. split.
  - eapply agree_below_trans; [exact Hag1 | exact Hag].
  - split; [exact Hsm|]. eapply Hst0; [exact Hag | apply mat_equiv_refl | exact HJ].
Qed.

Theorem sn_sum : ltac2:(tb__ "0|0|
S1S5SfQ40A1A1S8R2A1S14S0Vok;SeS0VJ0;SaR3R2A5SdS0VJ0;S4R3R2S9A6A4F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct sn_shape as (HlenP & HnP & HnC & HnCS & _ & HnI & HlF & HnF & HbF & HnRG & Hge).
  apply (triple_pre ok _ (Forall (holds rho) facts_sn)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_sn w Hsm) | intros HF0].

  eapply (runA_tr segs ok FUEL_SN CUTS_SN Pre_sn _ J0 rho tp); [exact sn_run_call | exact HlenP | exact Hok | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_sn Hag1 HbF HF0) as HF1.
  eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_callS rho1 tp);
    [intros w [Hsm HJ]; apply (SPA_split segs _ rho1 E_call 0 (SLit (-32)) _ tp w sn_split_call); split;
       [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].

  apply (call_soundA segs ok (Jf J0 rho1 tp) (Jmc J0 rho1 tp) (Jmc J0 rho1 tp) (Jf J0 rho1 tp) E_callS Pre_mci s_call R_call Posts_mci _ rho1 tp sn_efr_call sn_chk_call).
  - intros rho2 tp2. apply (triple_pre ok _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (mci_sum ok (Jmc J0 rho1 tp) (Jmc_okf ok J0 Hok rho1 tp) (Jmc_stable J0 Hst0 rho1 tp) rho2 tp2 HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call_sn. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [| split; [reflexivity | exact HJ']].
    rewrite <- HnCS. exact (proj1 HLK).
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite sn_imp_call. rewrite HnCS in Hag'.
    apply (triple_pre ok _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
    pose proof (Forall_holds_agree NF rho1 rho' facts_sn Hag' HbF HF1) as HF'.
    eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_sn T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].

    eapply (runA_tr segs ok FUEL_SN CUTS_SN T_impF _ (Jf J0 rho1 tp) rho' tp);
      [exact sn_run_ret | exact HlF | apply (Jf_okf ok J0 Hok) | rewrite HnF; apply (Jf_stable J0 Hst0); unfold NF; lia |].
    intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnF in HagR.
    intros n Hg w HS. apply Hg. apply (SPA_axforms segs _ XN rhoR R_sn G_sn tp w sn_xf) in HS.
    assert (Hag3 : agree_below NF rho1 rhoR).
    { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
    exact (to_post_sn G_sn sp_sn rho rho1 tp rhoR w sn_ent sn_ids Hag1 Hag3 HS).
Qed.

Theorem sn_sum_ex : ltac2:(tb__ "0|0|
S1S5SfQ40A1A1S8R2A1S13S0SeS0VJ0;SaR3R2A5SdS0VJ0;S4R3R2S9A6A3F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct sn_shape as (HlenP & HnP & HnC & HnCS & _ & HnI & HlF & HnF & HbF & HnRG & Hge).
  apply (etriple_pre _ (Forall (holds rho) facts_sn)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_sn w Hsm) | intros HF0].
  eapply (erunA_tr segs FUEL_SN CUTS_SN Pre_sn _ J0 rho tp); [exact sn_run_call | exact HlenP | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_sn Hag1 HbF HF0) as HF1.
  eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_callS rho1 tp);
    [intros w [Hsm HJ]; apply (SPA_split segs _ rho1 E_call 0 (SLit (-32)) _ tp w sn_split_call); split;
       [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].
  apply (call_completeA segs (Jf J0 rho1 tp) (Jmc J0 rho1 tp) (Jmc J0 rho1 tp) (Jf J0 rho1 tp) E_callS Pre_mci s_call R_call Posts_mci _ rho1 tp sn_efr_call sn_chk_call).
  - intros rho2 tp2. apply (etriple_pre _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (mci_sum_ex (Jmc J0 rho1 tp) (Jmc_stable J0 Hst0 rho1 tp) rho2 tp2 HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call_sn. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [| split; [reflexivity | exact HJ']].
    rewrite <- HnCS. exact (proj1 HLK).
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite sn_imp_call. rewrite HnCS in Hag'.
    apply (etriple_pre _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
    pose proof (Forall_holds_agree NF rho1 rho' facts_sn Hag' HbF HF1) as HF'.
    eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_sn T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
    eapply (erunA_tr segs FUEL_SN CUTS_SN T_impF _ (Jf J0 rho1 tp) rho' tp);
      [exact sn_run_ret | exact HlF | rewrite HnF; apply (Jf_stable J0 Hst0); unfold NF; lia |].
    intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnF in HagR.
    intros w HS. exists w. split; [apply wsteps_refl|]. apply (SPA_axforms segs _ XN rhoR R_sn G_sn tp w sn_xf) in HS.
    assert (Hag3 : agree_below NF rho1 rhoR).
    { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
    exact (to_post_sn G_sn sp_sn rho rho1 tp rhoR w sn_ent sn_ids Hag1 Hag3 HS).
Qed.
End SN.
End Str_strnlenA.

(* [comment removed for export] *)
Module Icpt_strnlen.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "agree_below"; "holds"; "sprop"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA"; "FirstNul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st"; "Posts_si"; "Pre_si"; "P_si"; "facts_si"; "s_call"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Icpt_memchr"; "Jf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "facts_mci"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "entailsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform StrBytes MuslWL.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Icpt_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Str_strnlenA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Lemma facts_si_mci : ltac2:(tb__ "0|0|
S1S14S4S3R1A1SeA3S14S4S3R2A1S17A3F_;Fr;").
Proof. intros r HF. unfold facts_si in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Section SI.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Hypothesis Hok : ok_frameA segs ok J0.
Hypothesis Hst0 : stableA segs NF J0.

Lemma FirstNul_call_si : ltac2:(tb__ "0|0|
S1S7S5A1S15SaR3A1SaS1cS1bR4R3R2A3SfA2A1F_;Fms;FR;Frho;").
Proof.
  intros rho R ms [H0 H1]. destruct si_shape_call as (_ & _ & _ & _ & S16 & _). unfold FirstNul.
  change (rw (rho_sub (rho_absorb rho R ms) s_call) 16) with (eval (rho_absorb rho R ms) (wsub_get s_call 16)). rewrite S16.
  cbn [eval rw rl rho_sub rho_absorb]. split; assumption.
Qed.

Lemma to_post_si : ltac2:(tb__ "0|0|
S1fS1dS1S1S7S12Q40A1A1S1S1aS13S8S20R7SdR6A3S9A3S13S8S1eR7S6A2S9A3S2S6R7R6A3S2S6R7R5A3S11S0S16VJ0;R8R7A3RbR6R7R5A6S10S0VJ0;S6RaR8SbR6A7F_;F_;F_;F_;F_;Fw;FrhoR;Ftp;Frho1;Frho;Fsp;FG;").
Proof.
  intros G sp rho rho1 tp rhoR w Hent Hid Hag1 HagR HS.
  pose proof (SPA_entails segs (Jf J0 rho1 tp) NF G P_si sp rhoR tp w Hent Hid (Jf_stable J0 Hst0 rho1 tp NF (Pos.le_refl _)) HS) as [Hsm (Hag & _ & HJ)].
  exists (mkLeafA P_si RsSymJump), (rho_sub rhoR sp). split; [left; reflexivity|]. split.
  - eapply agree_below_trans; [exact Hag1 | exact Hag].
  - split; [exact Hsm|]. eapply Hst0; [exact Hag | apply mat_equiv_refl | exact HJ].
Qed.

Theorem si_sum : ltac2:(tb__ "0|0|
S1S7S12Q40A1A1SaR2A1S19S0Vok;S11S0VJ0;ScR3R2A5S10S0VJ0;S6R3R2SbA6A4F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct si_shape_call as (HlenP & HnP & HnC & HnCS & _ & HbF). destruct si_shape_imp as (HnI & HlS & HnS & HlB & HnB & Hf140 & HbS & HbB).
  destruct si_shape_rip as (HnRS & HnTr & HlTF & HnTF & HnE & HbTF). destruct si_shape_ret as (HnRS' & HnRB & HgeS & HgeB). destruct si_ids as [IdS IdB].
  apply (triple_pre ok _ (Forall (holds rho) facts_si)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_si w Hsm) | intros HF0].

  eapply (runA_tr segs ok FUEL_SI CUTS_SI Pre_si _ J0 rho tp); [exact si_run_call | exact HlenP | exact Hok | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_si Hag1 HbF HF0) as HF1.
  eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_callS rho1 tp);
    [intros w [Hsm HJ]; apply (SPA_split segs _ rho1 E_call 0 (SLit (- F_SI)) _ tp w si_split_call); split;
       [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].

  apply (call_soundA segs ok (Jf J0 rho1 tp) (Jmc J0 rho1 tp) (Jmc J0 rho1 tp) (Jf J0 rho1 tp) E_callS Pre_sn s_call R_call Posts_sn _ rho1 tp si_efr_call si_chk_call).
  - intros rho2 tp2. apply (triple_pre ok _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (sn_sum ok (Jmc J0 rho1 tp) (Jmc_okf ok J0 Hok rho1 tp) (Jmc_stable J0 Hst0 rho1 tp) rho2 tp2 HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call_si. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [| split; [reflexivity | exact HJ']].
    rewrite <- HnCS. exact (proj1 HLK).
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite si_imp_call. rewrite HnCS in Hag'.
    apply (triple_pre ok _ (tpL = tp /\ Forall (holds rho') (ss_facts (ax_S T_imp))));
      [intros w [Hsm (_ & E & _)]; split; [exact E | exact (smatchA_facts segs _ _ _ w Hsm)] | intros [-> HFi]].
    pose proof (Forall_holds_agree NF rho1 rho' facts_si Hag' HbF HF1) as HF'. pose proof (facts_si_mci rho' HF') as HFm'.
    assert (H140 : rw rho' 140 = rw rho' 16) by exact (holds_fact rho' _ _ HFi Hf140).
    assert (Hz' : rw rho' 16 = rw rho 16).
    { destruct Hag1 as (A1 & _ & _). destruct Hag' as (A2 & _ & _). rewrite <- (A2 16%positive ltac:(reflexivity)), <- (A1 16%positive ltac:(reflexivity)). reflexivity. }
    eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_si T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
    destruct (Z_lt_le_dec (bv_unsigned (rw rho 16) + 1) 65) as [HzS|HzB].
    +
      assert (HFS : Forall (holds rho') factsS).
      { unfold factsS. constructor; [apply (GEU65_S rho' H140); rewrite Hz'; lia | exact (post_facts_hold rho' HFm' H140)]. }
      eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_S rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsS T_impF w HFS ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (runA_tr segs ok FUEL_SI CUTS_SI T_S _ (Jf J0 rho1 tp) rho' tp);
        [exact si_run_S | exact HlS | apply (Jf_okf ok J0 Hok) | rewrite HnS; apply (Jf_stable J0 Hst0); unfold NF; lia |].
      intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnS in HagR.
      intros n Hg w HS. apply Hg. apply (SPA_axforms segs _ XS4 rhoR R_S G_S tp w si_xf_S) in HS.
      assert (Hag3 : agree_below NF rho1 rhoR).
      { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
      exact (to_post_si G_S sp_S rho rho1 tp rhoR w si_ent_S IdS Hag1 Hag3 HS).
    +
      assert (HFB : Forall (holds rho') factsB).
      { unfold factsB. constructor; [apply (GEU65_B rho' HFm' H140); rewrite Hz'; lia |].
        apply Forall_app. split; [exact (post_facts_hold rho' HFm' H140) | apply (big_facts_hold rho' HFm' H140); rewrite Hz'; lia]. }
      eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_B rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsB T_impF w HFB ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (runA_tr segs ok FUEL_SI CUTS_SI T_B _ (Jf J0 rho1 tp) rho' tp);
        [exact si_run_B | exact HlB | apply (Jf_okf ok J0 Hok) | rewrite HnB; apply (Jf_stable J0 Hst0); unfold NF; lia |].
      intros L2 rhoE [<-|[]] HagE. cbn [la_state]. rewrite HnB in HagE.
      eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_ripS rhoE tp);
        [intros w HS; exact (SPA_split segs _ rhoE E_rip 0 (SLit (-80)) _ tp w si_split_rip HS) | intros w Hw; exact Hw |].
      apply (call_soundA segs ok (Jf J0 rho1 tp) (Jz J0 rho1 tp) (Jz J0 rho1 tp) (Jf J0 rho1 tp) E_ripS Pre_rip s_rip R_rip Posts_rip _ rhoE tp si_efr_rip si_chk_rip).
      * intros rho2 tp2. exact (region_sum ok (Jz J0 rho1 tp) rho2 tp2 (Jz_okf ok J0 Hok rho1 tp) (Jz_stable J0 Hst0 rho1 tp NF)).
      * intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity | exact HJ].
      * intros L rho'' rhoL tpL tr ms md tr' md' HinL Hsm (HagE' & _ & _) HLK [-> HJ']. split; [| split; [reflexivity | exact HJ']].
        eapply agree_below_trans; [exact HagE' |]. eapply agree_below_le; [| exact (proj1 HLK)]. rewrite HnRS. apply Pos.leb_le in HnE. unfold NF in *; lia.
      * intros L rho'' tpL [<-|[]] Hag''. cbn [la_state]. rewrite si_imp_rip. rewrite HnRS in Hag''. apply Pos.leb_le in HnE.
        apply (triple_pre ok _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
        assert (HF'' : Forall (holds rho'') (SPEq (SVar 140) (SVar 16) :: facts_si)).
        { apply (Forall_holds_agree 141 rho' rho''); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | constructor; [exact (holds_fact rho' _ _ HFi Hf140) | exact HF']].
          eapply agree_below_trans; [exact HagE | eapply agree_below_le; [exact HnE | exact Hag'']]. }
        eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_ripF rho'' tp);
          [intros w HS; exact (SPA_add_facts _ rho'' tp _ T_rip w HF'' ltac:(rewrite HnTr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
        eapply (runA_tr segs ok FUEL_SI CUTS_SI T_ripF _ (Jf J0 rho1 tp) rho'' tp);
          [exact si_run_B2 | exact HlTF | apply (Jf_okf ok J0 Hok) | rewrite HnTF; apply (Jf_stable J0 Hst0); unfold NF; lia |].
        intros L3 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnTF in HagR.
        intros n Hg w HS. apply Hg. apply (SPA_axforms segs _ XB4 rhoR R_B G_B tp w si_xf_B) in HS.
        assert (Hag3 : agree_below NF rho1 rhoR).
        { eapply agree_below_trans; [exact Hag' |]. eapply agree_below_trans; [eapply agree_below_le; [| exact HagE]; unfold NF; lia |].
          eapply agree_below_trans; [eapply agree_below_le; [| exact Hag'']; unfold NF; lia | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
        exact (to_post_si G_B sp_B rho rho1 tp rhoR w si_ent_B IdB Hag1 Hag3 HS).
Qed.

Theorem si_sum_ex : ltac2:(tb__ "0|0|
S1S7S12Q40A1A1SaR2A1S18S0S11S0VJ0;ScR3R2A5S10S0VJ0;S6R3R2SbA6A3F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct si_shape_call as (HlenP & HnP & HnC & HnCS & _ & HbF). destruct si_shape_imp as (HnI & HlS & HnS & HlB & HnB & Hf140 & HbS & HbB).
  destruct si_shape_rip as (HnRS & HnTr & HlTF & HnTF & HnE & HbTF). destruct si_shape_ret as (HnRS' & HnRB & HgeS & HgeB). destruct si_ids as [IdS IdB].
  apply (etriple_pre _ (Forall (holds rho) facts_si)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_si w Hsm) | intros HF0].
  eapply (erunA_tr segs FUEL_SI CUTS_SI Pre_si _ J0 rho tp); [exact si_run_call | exact HlenP | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_si Hag1 HbF HF0) as HF1.
  eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_callS rho1 tp);
    [intros w [Hsm HJ]; apply (SPA_split segs _ rho1 E_call 0 (SLit (- F_SI)) _ tp w si_split_call); split;
       [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].
  apply (call_completeA segs (Jf J0 rho1 tp) (Jmc J0 rho1 tp) (Jmc J0 rho1 tp) (Jf J0 rho1 tp) E_callS Pre_sn s_call R_call Posts_sn _ rho1 tp si_efr_call si_chk_call).
  - intros rho2 tp2. apply (etriple_pre _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (sn_sum_ex (Jmc J0 rho1 tp) (Jmc_stable J0 Hst0 rho1 tp) rho2 tp2 HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call_si. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [| split; [reflexivity | exact HJ']].
    rewrite <- HnCS. exact (proj1 HLK).
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite si_imp_call. rewrite HnCS in Hag'.
    apply (etriple_pre _ (tpL = tp /\ Forall (holds rho') (ss_facts (ax_S T_imp))));
      [intros w [Hsm (_ & E & _)]; split; [exact E | exact (smatchA_facts segs _ _ _ w Hsm)] | intros [-> HFi]].
    pose proof (Forall_holds_agree NF rho1 rho' facts_si Hag' HbF HF1) as HF'. pose proof (facts_si_mci rho' HF') as HFm'.
    assert (H140 : rw rho' 140 = rw rho' 16) by exact (holds_fact rho' _ _ HFi Hf140).
    assert (Hz' : rw rho' 16 = rw rho 16).
    { destruct Hag1 as (A1 & _ & _). destruct Hag' as (A2 & _ & _). rewrite <- (A2 16%positive ltac:(reflexivity)), <- (A1 16%positive ltac:(reflexivity)). reflexivity. }
    eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_si T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
    destruct (Z_lt_le_dec (bv_unsigned (rw rho 16) + 1) 65) as [HzS|HzB].
    + assert (HFS : Forall (holds rho') factsS).
      { unfold factsS. constructor; [apply (GEU65_S rho' H140); rewrite Hz'; lia | exact (post_facts_hold rho' HFm' H140)]. }
      eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_S rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsS T_impF w HFS ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (erunA_tr segs FUEL_SI CUTS_SI T_S _ (Jf J0 rho1 tp) rho' tp);
        [exact si_run_S | exact HlS | rewrite HnS; apply (Jf_stable J0 Hst0); unfold NF; lia |].
      intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnS in HagR.
      intros w HS. exists w. split; [apply wsteps_refl|]. apply (SPA_axforms segs _ XS4 rhoR R_S G_S tp w si_xf_S) in HS.
      assert (Hag3 : agree_below NF rho1 rhoR).
      { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
      exact (to_post_si G_S sp_S rho rho1 tp rhoR w si_ent_S IdS Hag1 Hag3 HS).
    + assert (HFB : Forall (holds rho') factsB).
      { unfold factsB. constructor; [apply (GEU65_B rho' HFm' H140); rewrite Hz'; lia |].
        apply Forall_app. split; [exact (post_facts_hold rho' HFm' H140) | apply (big_facts_hold rho' HFm' H140); rewrite Hz'; lia]. }
      eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_B rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsB T_impF w HFB ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (erunA_tr segs FUEL_SI CUTS_SI T_B _ (Jf J0 rho1 tp) rho' tp);
        [exact si_run_B | exact HlB | rewrite HnB; apply (Jf_stable J0 Hst0); unfold NF; lia |].
      intros L2 rhoE [<-|[]] HagE. cbn [la_state]. rewrite HnB in HagE.
      eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_ripS rhoE tp);
        [intros w HS; exact (SPA_split segs _ rhoE E_rip 0 (SLit (-80)) _ tp w si_split_rip HS) | intros w Hw; exact Hw |].
      apply (call_completeA segs (Jf J0 rho1 tp) (Jz J0 rho1 tp) (Jz J0 rho1 tp) (Jf J0 rho1 tp) E_ripS Pre_rip s_rip R_rip Posts_rip _ rhoE tp si_efr_rip si_chk_rip).
      * intros rho2 tp2. exact (region_sum_ex (Jz J0 rho1 tp) rho2 tp2 (Jz_stable J0 Hst0 rho1 tp NF)).
      * intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity | exact HJ].
      * intros L rho'' rhoL tpL tr ms md tr' md' HinL Hsm (HagE' & _ & _) HLK [-> HJ']. split; [| split; [reflexivity | exact HJ']].
        eapply agree_below_trans; [exact HagE' |]. eapply agree_below_le; [| exact (proj1 HLK)]. rewrite HnRS. apply Pos.leb_le in HnE. unfold NF in *; lia.
      * intros L rho'' tpL [<-|[]] Hag''. cbn [la_state]. rewrite si_imp_rip. rewrite HnRS in Hag''. apply Pos.leb_le in HnE.
        apply (etriple_pre _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
        assert (HF'' : Forall (holds rho'') (SPEq (SVar 140) (SVar 16) :: facts_si)).
        { apply (Forall_holds_agree 141 rho' rho''); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | constructor; [exact (holds_fact rho' _ _ HFi Hf140) | exact HF']].
          eapply agree_below_trans; [exact HagE | eapply agree_below_le; [exact HnE | exact Hag'']]. }
        eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_ripF rho'' tp);
          [intros w HS; exact (SPA_add_facts _ rho'' tp _ T_rip w HF'' ltac:(rewrite HnTr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
        eapply (erunA_tr segs FUEL_SI CUTS_SI T_ripF _ (Jf J0 rho1 tp) rho'' tp);
          [exact si_run_B2 | exact HlTF | rewrite HnTF; apply (Jf_stable J0 Hst0); unfold NF; lia |].
        intros L3 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnTF in HagR.
        intros w HS. exists w. split; [apply wsteps_refl|]. apply (SPA_axforms segs _ XB4 rhoR R_B G_B tp w si_xf_B) in HS.
        assert (Hag3 : agree_below NF rho1 rhoR).
        { eapply agree_below_trans; [exact Hag' |]. eapply agree_below_trans; [eapply agree_below_le; [| exact HagE]; unfold NF; lia |].
          eapply agree_below_trans; [eapply agree_below_le; [| exact Hag'']; unfold NF; lia | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
        exact (to_post_si G_B sp_B rho rho1 tp rhoR w si_ent_B IdB Hag1 Hag3 HS).
Qed.
End SI.
End Icpt_strnlen.

(* [comment removed for export] *)
Module Asan_memcpyR.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "app"; "bool"; "list"; "pair"; "true"; "nat"; "prod"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "SVar"; "valuation"; "DUnknown"; "FcsrFrm0"; "cell"; "mkObj"; "mkSS"; "ss_objs"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "A_globals"; "mkA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Asan_memcpyR"; "CR"; "PR"; "objsLR"; "FUELR"; "PostsR"; "PreWR"; "vcutsR"; "vexitsR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "cut_regs"; "pre_fregs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_memcpy_contract"; "R_rtc"; "carve_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "NPOSTM"; "ae_ret_asan_memcpy"; "memx_depth"; "pre_facts"; "stack_win"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface"; "L_memcpyR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_memcpy_contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_memcpy_contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
Import ListNotations.
Close Scope bv_scope. Open Scope Z_scope.

Definition PreWR (src : Z) : axst := Pre_memcpyR AE_A src 12.
Definition CR (src : Z) : axst := ltac2:(tb__ "0|1|
S2dS21Vsrc;A1M0S31S2bG0A1A1A2").

Definition objsLR : list sobj := ltac2:(tb__ "0|0|
S2ScS0ScS39S0ScS13SePcA1SdZ0A1SdZcA1S1S12A1S10A5S1ScA1A3A3S18A3").
Definition PR (src : Z) : axst := ltac2:(tb__ "0|2|
S19S14S36S34A1S27S25S24A1S0S8S7SbA2M0S5S7SbUaSePcA1A4S1G0A1A3A2S26S11S9SbA1S2ScS1eS30A3S38S37A1S35SaA9S0S8SbSbA2M1S5SbSbSeP35A1SeP36A1A4S0G1S5SbSbSdVsrc;A1SdZcA1A4S1G1A1A3A3A2").
Definition PostsR (src : Z) : list leafA := ltac2:(tb__ "0|0|
S0S2eS2fS1dVsrc;A1S3eA2S1S2eA1A3").

Lemma PR_objs : ltac2:(tb__ "0|0|
S1bS1aS4ScA1S15S2bS1dR1A1A1A1S2ScS1eS30A3A3Fsrc;"). Proof. reflexivity. Qed.

Lemma PR_unobj : ltac2:(tb__ "0|1|
S1bS1aS2cS2dS1dR1A1M0S3fS2bG0A1S1eA2A2S3bS34R1ZcA3A3Fsrc;"). Proof. reflexivity. Qed.
Lemma swf_CR : ltac2:(tb__ "0|0|
S1bS1aS3S16S2bS1cR1A1A1A1S6A3Fsrc;"). Proof. intros src. reflexivity. Qed.

Definition FUELR : nat := 1500%nat.
Definition vcutsR (src : Z) : list vnodeA := ltac2:(tb__ "0|0|
S0S28S29S1cVsrc;A1Z1SdZ0A1A3S1S28A1A3").
Definition vexitsR (src : Z) : list vnodeA := ltac2:(tb__ "0|0|
S0S28S29S1dVsrc;A1Z0SdZ1A1A3S1S28A1A3").
Definition certR (src : Z) : Prop := ltac2:(tb__ "0|0|
S1aS3S40S17S1fS1S1bA1S24S22Vsrc;A1S23Vsrc;A1A6S6A3").

Lemma echeckR_hv : certR white_hv. Proof. unfold certR. vm_cast_no_check (eq_refl true). Qed.
Lemma echeckR_lo : certR white_lo. Proof. unfold certR. vm_cast_no_check (eq_refl true). Qed.

Section Core.
Variable src : Z.
Hypothesis Hcert : certR src.

Lemma checkR : ltac2:(tb__ "0|1|
S1aS3S2aS17S1fS1S1bA1S24S0S2cS1cVsrc;A1S1S2cA1M0A3S0S2cS1dVsrc;A1G0A3A6S6A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELR [] NF (vcutsR src) (vexitsR src) [CR src] [PR src] eq_refl eq_refl Hcert). Qed.

Section Sum.
Variable ok : world -> Prop.
Variable J : jpredA.
Hypothesis Hok : ok_frameA segs ok J.
Hypothesis Hst : stableA segs NF J.

Theorem coreR_sum : ltac2:(tb__ "0|0|
SfS4S3aQ40A1A1S3dS17Vok;S33S17VJ;S1cVsrc;A1R2R1A5S32S17VJ;S24R2R1S20Vsrc;A1A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF (CR src) rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELR [] NF [CR src] [PR src] (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp (PostsR src)) tp HokG HstG checkR); [|left; reflexivity].
  intros E rhoE HinE. destruct HinE as [<-|[]]. apply exit_postA. left; reflexivity.
Qed.
End Sum.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.

Theorem coreR_sum_ex : ltac2:(tb__ "0|0|
SfS4S3aQ40A1A1S3cS17S33S17VJ;S1cVsrc;A1R2R1A5S32S17VJ;S24R2R1S20Vsrc;A1A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF (CR src) rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_complete_autoIA segs FUELR [] NF (vcutsR src) (vexitsR src) (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp (PostsR src)) tp HstG) with (n := mkVNA (CR src) 1 (SLit 0)); [ | exact Hcert | | left; reflexivity].
  { intros m [<-|[]]. apply Pos.le_refl. }
  intros E rhoE HinE. destruct HinE as [<-|[]].
  apply (eexit_post_IA0 segs J NF rho (vcutsR src) (PostsR src) (mkVNA (PR src) 0 (SLit 1))). left; reflexivity.
Qed.
End SumEx.
End Core.
End Asan_memcpyR.

(* [comment removed for export] *)
Module Lib_vec_finalize_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "cons"; "bool"; "nil"; "false"; "true"; "Some"; "app"; "fst"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "holds"; "ss_facts"; "SLit"; "sv_eqb"; "ss_next"; "ob_base"; "ob_hi"; "ob_lo"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "AHead"; "am_subst"; "amode"; "emeasA"; "JA"; "JLA"; "ejcertA"; "nodeIA"; "ok_frameKA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_subA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "BXok_d"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_finalize"; "E_call"; "s_call"; "nd0"; "R_call"; "X_go"; "vL"; "vV"; "P_fail"; "P_ok"; "Xk_call"; "nd_zero"; "vD"; "P_zero"; "P_zero2"; "Pre_vf"; "cutsV"; "exitsV"; "go_facts"; "nd_fail"; "nd_ok"; "tv_vf"; "C_go"; "FUEL_vf"; "cutpcs_vf"; "vHDn"; "vHDv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup"; "Pre_ad"; "am_np"; "am_ok"; "ndF"; "ndK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_vec_finalize_pf"; "P0_vf"; "PD_adv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_finalize.Lib_arena_dup"; "P_fail"; "P_ok"; "tv0"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_vec_finalize_pf.Sum"; "JL"; "Posts_vf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "FFx"; "T_afterA3"; "PostsC"; "robjs_okF"; "xr_eqb"; "xrs_okF"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_vec_finalize_dup_pf"; "P0_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_finalize.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_vec_finalize_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_vec_finalize_dup_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import VFAddr ADAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma C_go_eq : ltac2:(tb__ "0|0|
S12S1S8aS45SdS17S52S19S2S45A1A1A3A2S56A3"). Proof. reflexivity. Qed.
Lemma P_fail_eq : ltac2:(tb__ "0|0|
S12S1S77S5bS41S42S44S6fS4aA6S48A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma P_ok_eq : ltac2:(tb__ "0|0|
S12S1S77S5bS41S42S44S70S4aA6S49A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition PD_adv : list (axst * ndesc) := ltac2:(tb__ "0|1|
S7S4S1S21A2M0S5S1S21S6fS5eA4S7G0S5S1S21S70S5fA4S9G0A1A3A3").
Lemma imp_fail_tv : ltac2:(tb__ "0|0|
S12S6S4S15S15A2A1S82S38S42S5bS6fS41A4S71A2S55A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ok_tv : ltac2:(tb__ "0|0|
S12S6S4S15S15A2A1S82S38S42S5bS70S41A4S71A2S55A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_am : ltac2:(tb__ "0|0|
S12S26S25S38S42S5bS6fS41A4S5cA2S24S5aSaA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ok_am : ltac2:(tb__ "0|0|
S12S26S25S38S42S5bS70S41A4S5dA2S24S59SbA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition P0_vf (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|5|
S11S0S11S2dS3eVr;S47A2M0R1A2S2fR1S2eG0Z20A2A2A2S75VCST;Vr;VFB;VFF;R2A5F_;Fa;S14S12S0S3eVr;S46A2M1Z0A3S14S13S0S0S13S0S0S11S3cS4S0S0A2M2S5S0S0R2R1A4VFB;A3S11S2dR2S3eVr;S4cA2M3A2S2dS2eG3G1A2M4S2eR2R1A2A2A2A2Ln;A2Lb;A2S13S0S0S13S0S0S13S0S0S11S3cS4G2S0A2S5G2S0S5S0S0R3R2A4R1A4VFF;A3S11S2dR3G3A2S2dG4S2eR3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2A2A2A2").
Definition is_vec (o : sobj) : bool := ltac2:(tb__ "0|1|
S8S8L_;M0S1bS1dVo;A1S47A2G0S1bS1fVo;A1S1aZ0A1A2S1bS1eVo;A1S1aZ20A1A2SaX8x2SaX8x2").
Definition is_vecX (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S7aVr;S5S15S15S47S1aZ20A1A4A2").

Lemma pclMA_monox : ltac2:(tb__ "0|2|
S6S4S0S0A2M0A1M1S16G1S6S4G0S0A2A1S16S6S4S15S15A2A1S6S4S4S15S0A2S15A2A1S0S75R8R7R6R5R1A5S75R9R8S81R7R5R4A3S76R6R5R3A3R2A5F_;Fa;Ffrs;Fkept;Frho;FFF;FFB;Frho0;FCST;").
Proof.
  intros CST rho0 FB FF rho kept frs a [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | exact Hr].
  - right; right; right. exists f, s, fl. split; [apply In_FFx; left; exact Hin | exact Hr].
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S8dS16S6S32Q40A1A1S67OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S87S10VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S88VCST;R1A2S11S2dZ0R2A2S2fR2S83A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S88VXGL;R1A2S11S2dZ0R2A2S2fR2S83A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S6S4S4S0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 4 BX.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S29VAInv;VCST;VXGL;VKc;S60VCST;VFB;VFF;A3VFB;VFF;VBX;S22Vnd;Aa").
Definition Posts_vf : list (axst * jpostA) := ltac2:(tb__ "0|2|
S7S4S1S36A2M0S5S1S36S4dS73S4bA1M1A4S7G0S5S1S36S48S73S53A1A4S7G0S5S1S36S49S73S54A1A4S7G0S5S1S36S4eG1A4S9G0A1A3A3A3A3").

Definition PD_vf : list (axst * ndesc) := ltac2:(tb__ "0|1|
S7S4S1S21A2M0S5S1S21S4dS4bA4S7G0S5S1S21S48S53A4S7G0S5S1S21S49S54A4S7G0S5S1S21S4eS4bA4S9G0A1A3A3A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S28VAInv;VCST;VXGL;S3dVKc;Vrho0;S60VCST;VFB;VFF;A3VFB;VFF;VBX;S22Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S4S1S21A2S89Fn;") := ltac2:(tb__ "0|0|
S2bVAInv;VCST;VXGL;S3dVKc;Vrho0;S60VCST;VFB;VFF;A3VFB;VFF;VBX;S22Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S37S10S3dVrho0;Vtp0;S74A5").

Lemma P0_now : ltac2:(tb__ "0|4|
S16S7fS3dVrho0;R1A3S60VCST;VFB;VFF;Vrho0;A4S11S0S11S2dS3eR4S47A2M0R1A2S2fR1S2eG0Z20A2A2A2S75VCST;Vrho0;VFB;VFF;R2A5F_;Fa;S14S12S0S3eR3S46A2Z0A3S14S13S0S0S13S0S0S11S3cS4S0S0A2M1S5S0S0R2R1A4VFB;A3S11S2dR2S3eR5S4cA2M2A2S2dS2eG2S3eR5S46A2A2S2eR2R1A2A2A2A2Ln;A2Lb;A2S13S0S0S13S0S0S13S0S0S11S3cS4G1S0A2S5G1S0S5S0S0R3R2A4R1A4VFF;A3S11S2dR3S3eR6S4cA2M3A2S2dS2eG3S3eR6S46A2A2S2eR3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav H. unfold P0_vf, uval, vV, vL, vD in *. cbn [eval] in *.
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 17%positive eq_refl). exact H.
Qed.

Lemma go_holds : ltac2:(tb__ "0|0|
S16S6S32Q40A1A1S6S68A1S67VJAv;S43R4R3R2R1A5S6cS17S18R5A1S19S2S45A1A1A3S6cS17S18R6A1S52A3F_;F_;Fmd;Ftr;Ftp;Frho;").
Proof.
  intros rho tp tr md (Ai & kc & HJ) HF.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & _ & _ & _ & HP0 & _).
  fact HF (SPBranch BC_EQ (SMd M_MULHU vC vE) (SLit 0)) F1. fact HF (SPNot (SPBranch BC_EQ vC (SLit 0))) F2.
  fact HF (SPUle (SLit 1) vE) F3. fact HF (SPUle eC vL) F4.
  apply (proj1 (holds_beq _ _ _)) in F1. apply (proj1 (holds_nbeq _ _ _)) in F2. rewrite h_ule in F3, F4.
  rewrite U_mulhu in F1. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)) in F1, F2.
  change (bv_unsigned (eval rho vC)) with (uval rho vC) in F1, F2. change (bv_unsigned (eval rho vE)) with (uval rho vE) in F1.
  rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia. rewrite uval_lit in F3 by lia.
  pose proof (uval_range rho vC) as RC. pose proof (uval_range rho vE) as RE. pose proof (uval_range rho vL) as RL. pose proof (uval_range rho vD) as RD.
  rewrite Z.shiftr_div_pow2 in F1 by lia. unfold M64v in F1.
  assert (HP : uval rho vC * uval rho vE < 2 ^ 64).
  { destruct (Z_lt_dec (uval rho vC * uval rho vE) (2 ^ 64)) as [L|L]; [exact L|]. exfalso.
    assert (1 <= uval rho vC * uval rho vE / 2 ^ 64) by (apply Z.div_le_lower_bound; lia).
    assert (uval rho vC * uval rho vE / 2 ^ 64 < 2 ^ 64) by (apply Z.div_lt_upper_bound; [lia|]; nia).
    rewrite Z.mod_small in F1 by lia. lia. }
  assert (EC : uval rho eC = uval rho vE * uval rho vC).
  { unfold eC, uval. rewrite U_mul. unfold M64v. change (bv_unsigned (eval rho vE)) with (uval rho vE). change (bv_unsigned (eval rho vC)) with (uval rho vC).
    rewrite Z.mod_small by nia. reflexivity. }
  assert (G1 : 1 <= uval rho eC) by (rewrite EC; nia).
  unfold go_facts. constructor; [|constructor; [|constructor]]; rewrite h_ule; rewrite uval_lit by lia; [|exact G1].

  destruct (P0_now rho Hav HP0) as [_ [HL|[(b & n & Hin & H1 & H2)|(f & s & fl & Hin & H1 & H2)]]]; [exfalso; lia| |].
  - destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & HBl & _). destruct (HBl b n (HB _ Hin)) as (_ & _ & B3 & _). lia.
  - destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & _ & HFr). destruct (HFr f s (proj1 (HFF _ _ _ Hin))) as (_ & _ & _ & F4' & _).
    unfold IMG_HI in F4'. lia.
Qed.

Lemma HIN_call : ltac2:(tb__ "0|2|
S16S6eS6cS17S18R2A1S19S2S41A1A1A3S60VCST;VFB;VFF;Vrho0;A4S7fS3dVrho0;R4A3S11S79VCST;Vrho0;VFB;VFF;R5S9S4S15S15A2A1M0S9S4S4S15S0A2S15A2A1M1S44A8S11S7bVCST;VXGL;Vrho0;VFB;VFF;R5G0G1S4aA9S7eVCST;S81VFB;R5G0A3S76VFF;R5G1A3S6aS69R5S44R4A3S42A2A4A2A2F_;F_;F_;Fms;Frho;").
Proof.
  intros rho ms HF HP0 Hav. destruct (P0_now rho Hav HP0) as [HV HD].
  split; [|split].
  - intros o a Ho Hr. cbn in Ho. destruct Ho as [<-|[]]. apply pclMA_monox. apply HV.
    unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi O_vec] in Hr. rewrite !soff_lit_small in Hr by lia. cbn [fst snd] in Hr. unfold uval, vV in *. lia.
  - intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha. rewrite uval_lit in Ha by lia. left. apply pclMA_monox. apply HV. unfold uval, vV in *. lia.
  - unfold P0_ad. intros a Ha. unfold uval, vSRC, vLS in Ha. cbn [eval] in Ha. rewrite !rw_call' in Ha.
    change (wsub_get s_call 13) with vD in Ha. change (wsub_get s_call 16) with vL in Ha.
    change (bv_unsigned (eval rho vD)) with (uval rho vD) in Ha. change (bv_unsigned (eval rho vL)) with (uval rho vL) in Ha.
    destruct HD as [HL|[(b & n & Hin & H1 & H2)|(f & s & fl & Hin & H1 & H2)]]; [exfalso; lia| |].
    + right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | lia].
    + right; right; right. exists f, s, fl. split; [apply In_FFx; left; exact Hin | lia].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S6S32Q40A1A1S62F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S34S1S16S6S32Q40A1A1S62S6cS17S18R3A1S19S2R4A1A1A3VTR;S33S10R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S62S62S62S65R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S34S34S1S1S6bS6S20A1M0S6S4S1S36A2M1A1S6S4S15S15A2M2A1S62S16S6S32Q40A1A1M3G2S3cG2R1R5A3S3cG2R2S3RbA1A3F_;Fr;S12SfG0A1S3bRaR9R8A3ScG0R7A2A3S12S8S3aRbRaR9R8S6dG1S1SeS1S36A2R7A4A5SbA3S16G3VTR;S33S10RfRdR2R1A5S37S10S1cS2RdA1A1R2R1RaA5A2Ftp1;Frho1;S6S68A1M4S6eS67S35S10R9R8R10S5G4S7cR3S7dR2R1A2A4A5R13RaR9R4R2A4R13S6aS69RbRfS66R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S1S36G4S6eS67S16G3G4S6eS67S3cG1S5S1S36RaR9A4R14A3S35S10R12R11R19S5G4S7cR9S7dR8R7A2A4A5R1cR13R12RaR8A4S7fS1cS2R1aA1A1S6aS69R14R18S66R9R13RaA3A3R19A2R8A3S35S10R9R8ReS5G4S7cR7S7dR6R5A2A4A5ReS6aS69R16R1aS66RbR15RcA3A3R1bA2R15RaR9R8R6A6S11S8bR17S66RcR16RdA3R1bR1cR1dR10R1eR19RbA9S16S80R18S66RdR17ReA3R1cR1dS2R1eA1S2R1fA1S2R11A1R1RcA9VTR;S33S10S39R11S6aS69R19R1dS66ReR18RfA3A3R1eA2R18RdRcA5S8cR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S33S10R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CAD : ltac2:(tb__ "0|1|
S6S4S0S0A2M0A1S6S4G0S0A2A1S40S16S6S32Q40A1A1S3fZ3R3A2VTR;S33S10S23VAInv;VCST;VXGL;VKc;S7eVCST;R6R5A3R6R5R4S22S72AaS5bR3R2A5S37S10S3dR3R2S78VAInv;VCST;VXGL;VKc;S7eVCST;A1S22S61R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S1S21S4S0S15A2M0S16S6S32Q40A1A1M1S0G1S3cS4S4S1S21A2M2G0A2S5G2G0S5S1S21R7R6A4R5A4S50A3S11S2dZ0S27S5G2G0S5S1S21R8R7A4R6A4R5A2M3A2S2fG3R3A2A2VTR;S33S10VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S1S21S16S6S32Q40A1A1M0S0G0S3cS4S1S36A2S5S1S36R6S73R5A1A4S74A3VTR;S33S10VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.
Ltac vmr := vm_compute; reflexivity.
Tactic Notation "innth" integer(n) := cbn [In cutsV exitsV Posts_vf PD_vf PD_adv]; do n right; left; reflexivity.

Lemma X_X_go : ltac2:(tb__ "0|1|
S16S6S32Q40A1A1M0S0G0S2dS30Z5aS31Z2Z40A2A2R2A2VTR;S33S10VJAv;S43A1S45R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_go nd0 (80, z0)); [innth 1 | meas]].
  intros w Hw. rewrite <- C_go_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
  intros tr md HJ HF. apply Forall_app. split; [exact (go_holds rho tp tr md HJ HF) | exact HF].
Qed.

Lemma X_E_call : ltac2:(tb__ "0|1|
S16S6S32Q40A1A1M0S0G0S2dS30Z46S31Z2Z40A2A2R2A2VTR;S33S10VJAv;S43A1S41R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF. unfold nd0. change tv_vf with ([] ++ tv_vf).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue HKc HBX (P0_ad CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_ad Lib_arena_dup.nd0 PD_adv NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CAD eq_refl
           E_call s_call R_call Xk_call rho tp [] tv_vf [] CHv [] am_vf (FAM b tp0)).
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - apply payA_of_bud_pay. vmr.
  - vmr.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK. exact (HIN_call rho ms HF' HP0 Hav).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_adv In] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am ndF ndK Lib_arena_dup.nd0 ND am_subst app].
    + rewrite P_fail_eq, imp_fail_tv, imp_fail_am. change (bd_subst _ []) with (@nil bitem). cbn [app]. apply POST. innth 1.
    + rewrite P_ok_eq, imp_ok_tv, imp_ok_am. change (bd_subst _ []) with (@nil bitem). cbn [app]. apply POST. innth 2.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S1S21S4S0S15A2M0S16S6S32Q40A1A1M1G1S3cS4S4S1S21A2M2G0A2S5G2G0S5S1S21R6R5A4R4A4S51A3VTR;S33S10VJAv;R6A1R7R4R3A5VFAM;S27S5G2G0S5S1S21R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsV] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[]]]]]]]; injection H as <- <- <-.
  - apply X_X_go. meas.
  - apply X_E_call. meas.
  - apply POST. innth 0.
  - apply POST. innth 1.
  - apply POST. innth 2.
  - apply POST. innth 3.
Qed.
End X.

Lemma ejcertV_ok : ltac2:(tb__ "0|0|
S12S8S2aS10S3dS57S58P64S50S51A7SbA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S2cS10VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S85S10S84VAInv;VCST;VXGL;A5").

Theorem vec_finalize_sum : ltac2:(tb__ "0|0|
S6S32Q40A1A1S64S10Vok;S33S10S23VAInv;VCST;VXGL;VKc;S60VCST;VFB;VFF;A3VFB;VFF;VBX;S22S43AaS4fVrho0;R1A5S37S10S3dVrho0;R1S74A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue HKc ALA FUEL_vf cutpcs_vf 100
                (map edropA cutsV) (map edropA exitsV) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertV_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsV)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (arena_dup_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue ok (map edropA cutsV) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_vf CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_vf P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S86S10S84VAInv;VCST;VXGL;A5").

Theorem vec_finalize_sum_ex : ltac2:(tb__ "0|0|
S6S32Q40A1A1S63S10S33S10S23VAInv;VCST;VXGL;VKc;S60VCST;VFB;VFF;A3VFB;VFF;VBX;S22S43AaS4fVrho0;R1A5S37S10S3dVrho0;R1S74A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue HKc ALA FUEL_vf cutpcs_vf 100 cutsV exitsV (Q tp0) ejcertV_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue) cutsV) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (arena_dup_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue cutsV T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_vf CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_vf P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_finalize_pf.

(* [comment removed for export] *)
Module Lib_handle_mtllib.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "app"; "list"; "option"; "None"; "Some"; "false"; "true"; "S"; "bool"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "cell"; "sprop"; "ss_objs"; "FcsrFrm0"; "mkSS"; "SPUle"; "mkCell"; "mkObj"; "DUnknown"; "DZero"; "SVar"; "ss_facts"; "SAlu"; "SExt"; "SPAlign"; "SPBranch"; "ob_base"; "ob_hi"; "ob_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "leafA"; "ax_setS"; "sym_runA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ANone"; "NDA"; "ejcertA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_handle_mtllib"; "z0"; "nd0"; "ndP"; "E_da"; "T_sm1"; "X_ml"; "C_pro0"; "E_sm0"; "FUEL_ml"; "X_pro"; "cutpcs_ml"; "ml_facts"; "C_epi"; "C_pre"; "C_pro"; "E_da0"; "O_F"; "O_Wm"; "O_cfg"; "P_fail"; "P_ok"; "T_da0"; "T_sm"; "X_rl"; "Y_da"; "objs_post"; "objs_pro"; "objs_sm1"; "optAp"; "qERR"; "sel_rel"; "BAD"; "C_rl"; "NZ32"; "Pre_ml"; "Pre_sm"; "R_da"; "R_sm"; "cells_pro"; "cfg_facts"; "cutsM"; "epi_state"; "exitsM"; "fr_ml"; "objs_ml"; "s_da"; "s_sm"; "sel_sm"; "xf_tda"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "xCFG"; "NPH"; "hF"; "HNEXT"; "O_cE"; "O_cP"; "O_text"; "P_hdr"; "hFL"; "hG"; "h_fregs"; "tI"; "handle_facts"; "tB"; "tL"; "@Corelib.Lists.ListDef"; "seq"; "map"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "segs"; "leavesA_at"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_handle_mtllib.HMLAddr"; "DW"; "FR"; "ml_ret"; "ml_PRO"; "ml_REL"; "ml_entry"; "sm1_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "O_al"; "P_alloc"; "P_st"; "vERR"; "vAL"; "vb"; "vc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Pre_da"; "P_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "spm"; "vDp"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "fs_frame_size"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "L_stack_malloc"; "Pre_stack_malloc"; "V_DEPTH"; "flagbyte_obj"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.DiagAppendAddr"; "da_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS";
"flag_carve_stateA"; "frame_open_stateA"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr DiagAppendAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module HMLAddr.
  Definition ml_entry : Z := 0xa0420.
  Definition sm1_pc : Z := 0x47c10.
  Definition ml_PRO : Z := 0xa0534.
  Definition ml_EPI : Z := 0xa09b8.
  Definition ml_REL : Z := 0xa0a64.
  Definition ml_ret : Z := 0xa0aa0.
  Definition ml_ra_da : Z := 0xa0950.
  Definition DW : Z := 4608.
  Definition FR : Z := 256.
End HMLAddr.
Import HMLAddr.

Definition FUEL_ml : nat := 300%nat.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S1cPaA1S11SaeS81A1A1S11Z0A1Vcells;S1aA5").
Definition O_Wm : sobj := ltac2:(tb__ "0|0|
S19S90S81A1S91S11Z0A1S2S12A1S1aA5").

Definition O_cfg : sobj := ltac2:(tb__ "0|1|
S19S68S11Z0A1S11Z90A1S0S12S18S11Z30A1Z4M0S11Z10101A1A3S0S12S18S11Z38A1G0S11ZffffffffA1A3S2S12A1A3A3S1bA5").
Definition cfg_facts : list sprop := ltac2:(tb__ "0|0|
S0S13S20P6dZ3A2S0S13S17S11S9aA1S68A2S0S13S17S1eSa1S68S11Z90A1A3S1cP1eA1A2S0S13S17S68S11S92A1A2S2S13A1A3A3A3A3").
Definition ml_facts : list sprop := ltac2:(tb__ "0|0|
S5S13S74S81S80A2S5eA3").
Definition X_ml : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3SfSfA2M0S1SfSfS8cS11Z518A1A4S0G0S1SfSfS8dS11Z10A1A4S0G0S1SfSfS8bS11Z30A1A4S0G0S1SfSfS75S76A4S0G0S1SfSfS68S11Z90A1A4S0G0S1SfSfS90S80A1S11S80A1A4S2G0A1A3A3A3A3A3A3").
Definition objs_ml (err : sv) (fcells : list cell) : list sobj := ltac2:(tb__ "0|0|
S5S10S0S10S47Vfcells;A1S0S10S48S0S10S88S0S10S6fS0S10S89Verr;A1S0S10S87S0S10S6dS73A1S0S10S6cS0S10S6eS0S10S49S2S10A1A3A3A3A3A3A3A3A3A3A3S7cA3").
Definition Pre_ml_S : sstate := ltac2:(tb__ "0|0|
S16S85S98S97S15S8SfA1S63S8aS2S12A1A2S42S69SaA9").
Definition Pre_ml : axst := mkA Pre_ml_S X_ml.
Definition nd0 : ndesc := ND [] [] [].

Definition cutpcs_ml : list Z := ltac2:(tb__ "0|0|
S0S2bS86S0S2bS83S0S2bSa3S0S2bS84S2S2bA1A3A3A3A3").
Definition BAD : axst := ltac2:(tb__ "0|1|
S7bS16Z0S2SfA1M0G0S15S8SfA1S2S10A1S2S13A1P1SaA9S2S3SfSfA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S7aS25Vk;S7eS3fS41VS;Vpc;A4S56A4").
Definition lvs (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S7S6S28A1M0A1S6S3S2bSa5A2M1A1Lx;S2aS7dS3fS41VS;SbA5G0S78S28G1S7fR1A4Ll;S2G1A1X7x2").
Definition shape (A : axst) : ltac2:(tb__ "0|0|
S6S3S3SfSfA2SfA2A1") := ltac2:(tb__ "0|1|
S78S10S3S3SfSfA2M0SfA2S10S1G0SfS1SfSfS22R1A1S24R1A1A4S23R1A1A4Lo;S14S26VA;A1A1A4").

Definition E_sm0 : axst := Eval vm_compute in leaf_at Pre_ml sm1_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 1.
Definition L_sm : axst := L_stack_malloc AE_A 1.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S3S2cSfA2S1S2cSfS9eS91A4S93PaS26S3eA1S26S5aA1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Goal lvs Pre_ml = [(sm1_pc, RsCut)] /\ entails_frA E_sm0 Pre_sm s_sm = Some R_sm /\ call_checkPA E_sm0 Pre_sm s_sm R_sm [L_sm] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.
Definition fr_ml : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S3S3SfS2bA2M0SfA2M1S1G0SfS1SfS2bS6aZ1A4S70A4S2G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S5S4S77U0Vi;A2S5S4S77ScVi;A1M0Sa0SeS10S14S26VA;A1A1A2G0A2A2S0S4Vi;S2S4A1A3A3A3").
Definition T_sm1 : axst := Eval vm_compute in optAp (apply_axforms T_sm [AXSelect (sel_last T_sm 3)]).
Definition objs_sm1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_sm1)).
Goal ss_objs (ax_S T_sm1) = objs_sm1 ++ [flagbyte_obj hFL [mkCell (SLit 0) 1 (SLit 1)]] /\ ax_X T_sm1 = X_ml ++ (hF, SLit 128) :: [] /\ ss_next (ax_S T_sm1) = hG.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 objs_sm1 X_ml 160 128.
Definition C_pro : axst := Eval vm_compute in ax_setX C_pro0 ((hF, SLit 0) :: ax_X C_pro0).

Definition X_pro : axst := Eval vm_compute in leaf_at C_pro ml_PRO 0.
Definition sh_pro : sobj := Eval vm_compute in last (ss_objs (ax_S X_pro)) O_Wm.
Definition objs_pro : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_pro)).
Goal lvs C_pro = [(ml_PRO, RsCut)] /\ sh_pro = shobj hG 0 16 (ob_cells sh_pro) DZero.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition C_pre : axst := Eval vm_compute in shadow_release_stateA X_pro objs_pro 160 [].
Definition E_da0 : axst := Eval vm_compute in leaf_at C_pre da_entry 0.
Goal lvs C_pre = [(da_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_da : axst := Eval vm_compute in optAp (apply_axforms E_da0 [AXSplit 0 (SLit (-96))]).
Definition s_da : wsub := ltac2:(tb__ "0|0|
S93PaS26S3aA1S26S8eA1A3").
Definition R_da : list sobj := Eval vm_compute in optR (entails_frA E_da Pre_da s_da).
Goal entails_frA E_da Pre_da s_da = Some R_da /\ call_checkA E_da Pre_da s_da R_da (map la_state Posts_da) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_pure (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S94S1dS26VCl;A1A1S95Vs;VPre;VL;VCl;VR;A5A2").
Definition T_da0 : axst := Eval vm_compute in T_pure Pre_da E_da s_da R_da P_da.

Definition xf_tda : list axform := ltac2:(tb__ "0|1|
S0S32S34S5S4S0S4U3S0S4U0M0S0S4U4S0S4U5S0S4U1S0S4U2S2S4A1A3A3A3A3A3A3S77U6U9A2A3A1S0S32S35G0A1S2S32A1A3A3").
Definition Y_da : axst := Eval vm_compute in optAp (apply_axforms T_da0 xf_tda).
Definition epi_state (Y : axst) : axst := ltac2:(tb__ "0|0|
Sa9SacVY;S27VY;A1S71Z0Z10A5PaaA2").
Definition C_epi : axst := Eval vm_compute in epi_state Y_da.

Definition X_rl : axst := Eval vm_compute in leaf_at C_epi ml_REL 0.
Definition sel_rel : list nat := ltac2:(tb__ "0|1|
S5S4S0S4U0S2S4A1M0A3S5S4S77U3UbA2S0S4U1S0S4U2S0S4UeS0S4UfG0A3A3A3A3A3A3").
Definition rel_state (X : axst) : axst := ltac2:(tb__ "0|1|
S53S33VX;S0S32S34S55A1S2S32A1A3A2A1S25S29R1Sa4S26R1A1M0S79S10UcS14G0A1A3A2A2TX1;").
Definition C_rl : axst := Eval vm_compute in rel_state X_rl.
Definition X_ret : axst := Eval vm_compute in leaf_at C_rl ml_ret 0.
Goal shape Y_da = shape E_da0 /\ lvs C_epi = [(ml_REL, RsCut)]
  /\ release_objs_ok 160 170 hG 1 (skipn 12 (ss_objs (ax_S (optAp (apply_axforms X_rl [AXSelect sel_rel]))))) = true
  /\ length (ss_objs (ax_S C_rl)) = 12%nat /\ lvs C_rl = [(ml_ret, RsSymJump)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition qERR : sv := SVar 315.
Definition objs_post (err : sv) : list sobj := ltac2:(tb__ "0|1|
S5S10S0S10S48S2S10A1M0A3S5S10S7cS0S10S47S2S12A1A1S0S10S88S0S10S6fS0S10S89Verr;A1S0S10S87S0S10S6dS73A1S0S10S6cS0S10S6eS0S10S49G0A3A3A3A3A3A3A3A3A3A3A3").
Definition NZ32 (e : sv) : sprop := ltac2:(tb__ "0|0|
S21Sa2S1fSbQ20Ve;A3S11Z0A1A3").
Definition P_ok : axst := ltac2:(tb__ "0|0|
S7bS16S82S96P190A1S72S15S8SfA1S50S8aA1S42S6bSaA9S3cA2").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S7bS16S82S96P190A1S72S15S8SfA1S50S54A1S0S13S58S54A1S42A3S6bSaA9S3cA2").
Definition Posts_ml : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S3S25S2dA2M0S1S25S2dS4aS38A4S0G0S1S25S2dS4bS38A4S2G0A1A3A3").
Goal leaf_matches1A NPH X_ret P_ok = true /\ leaf_matches1A NPH X_ret P_fail = false. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ndP : ndesc := ltac2:(tb__ "0|0|
S2fS2S3SfSfA2A1S62S2Sa7A1S2eA4").
Definition z0 : sv := SLit 0.
Definition cutsM : list edescA := ltac2:(tb__ "0|3|
S0S3S3S25S2dA2M0S3S2bSfA2M1A2M2S1G0G1S1S25S2dS59S38A4S1S2bSfZ64S37A4A4S0G2S1G0G1S1S25S2dS45S39A4S1S2bSfZ60S37A4A4S0G2S1G0G1S1S25S2dS44S39A4S1S2bSfZ5cS37A4A4S0G2S1G0G1S1S25S2dS43S39A4S1S2bSfZ32S37A4A4S0G2S1G0G1S1S25S2dS57S38A4S1S2bSfZ14S37A4A4S2G2A1A3A3A3A3A3").
Definition exitsM : list edescA := ltac2:(tb__ "0|4|
S0S3S3S25S2dA2M0S3S2bSfA2M1A2M2S1G0G1S1S25S2dS3eS38A4S1S2bSfZ62S37A4A4S0G2S1G0G1S1S25S2dS40S39A4S1S2bSfZ5eS37A4A4S0G2S1G0G1S1S25S2dS46S39A4S1S2bSfZ5aS37A4A4S0G2S1G0G1S1S25S2dS4eS39A4S1S2bSfZ1eS37A4A4S0G2S1G0G1S1S25S2dS4aS38A4S1S2bSfZ0S37A4M3A4S0G2S1G0G1S1S25S2dS4bS38A4G3A4S2G2A1A3A3A3A3A3A3").
Lemma ejcertM_ok : ltac2:(tb__ "0|0|
S31SdS30S7dS69S3fS41S69S5fS61A7SbA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma T_sm_eq : ltac2:(tb__ "0|1|
S31S25Sa8S9dS9bZ1M0A2S3eS65S5cS9cS9bG0A2A5S4dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sel_sm : list nat := Eval vm_compute in sel_last T_sm 3.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S31S7S25A1S33S4dS0S32S34S66A1S2S32A1A3A2S9S25S3bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_objs : ltac2:(tb__ "0|1|
S31S6S10A1S14S26S3bA1A1S5S10S52S0S10S9fS70S0S12S18S11Z0A1Z1M0S11G0A1A3S2S12A1A3A2S2S10A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_X : ltac2:(tb__ "0|1|
S31S6S3SfSfA2M0A1S27S3bA1S5G0S3cS0G0S1SfSfS6aS11S99Z1A1A1A4S2G0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|0|
S31S25SaaS3bS52S3cPa0S99Z1A1A5S3dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro_eq : ltac2:(tb__ "0|0|
S31S25Sa6S3dS0S3SfSfA2S1SfSfS6aS11Z0A1A4S27S3dA1A3A2S45A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition cells_pro : list cell := Eval vm_compute in ob_cells sh_pro.
Lemma X_pro_objs : ltac2:(tb__ "0|0|
S31S6S10A1S14S26S40A1A1S5S10S51S0S10SadS71Z0Z10S5dS1bA5S2S10A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pre_eq : ltac2:(tb__ "0|0|
S31S25SabS40S51Pa0S2S3S2bS2bA2A1A4S44A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_da_eq : ltac2:(tb__ "0|0|
S31S7S25A1S33S46S0S32S36U0S11N60A1A2S2S32A1A3A2S9S25S3aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da0_eq : ltac2:(tb__ "0|0|
S31S25S94S1dS26S3aA1A1S95S64S8eS8fS3aS5bA5A2S4cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_da_eq : ltac2:(tb__ "0|0|
S31S7S25A1S33S4cS67A2S9S25S4fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_epi_eq : ltac2:(tb__ "0|0|
S31S25S60S4fA1S43A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rl_eq : ltac2:(tb__ "0|1|
S31S7S25A1S33S4eS0S32S34S55A1S2S32A1A3A2M0S9S25S53G0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_handle_mtllib.

