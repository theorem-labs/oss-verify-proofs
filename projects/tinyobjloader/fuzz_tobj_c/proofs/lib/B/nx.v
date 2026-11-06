(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Fps_tailR.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ns.

(* [comment removed for export] *)
Module FpsU_a5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsU_st"; "T7b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "PRE_U"; "SUF_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Fps_tailR"; "tailAR_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsB"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Fps_tailR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsU_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Fps_tailR.
Import ListNotations.
Open Scope Z_scope.

Lemma okR_5 : ltac2:(tb__ "0|0|
S5S2SbS0S0S9S7S8Z7R1Z0SaS6A7Ln;S1S0Z41S1S0Z42S3S0A1A3A3A3S4A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsU_a5.

(* [comment removed for export] *)
Module Fps_tailBdefs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "andb"; "option"; "bool"; "cons"; "false"; "negb"; "nil"; "length"; "list"; "pair"; "None"; "orb"; "Some"; "app"; "true"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sstate"; "ss_next"; "sobj"; "sv_eqb"; "sprop"; "cell"; "reg_sv"; "ss_objs"; "ss_lenient"; "SAlu"; "SVar"; "mkCell"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_pc"; "swf"; "DList"; "DRom"; "dflt_writable"; "is_arr"; "mkObj"; "sprop_eqb"; "ss_facts"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_base"; "cell_eqb"; "ax_setS"; "dflt_eqb"; "entailsA"; "sobj_eqb"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "add"; "eqb"; "of_nat"; "pow"; "opp"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nx.Fps_tailBdefs"; "tailB_out"; "tailBR_out"; "O_sufR"; "tailB_post"; "FSB"; "TBO"; "TBRO"; "finishB"; "iov01_ok"; "obj_far"; "splitsB"; "subB"; "tailB"; "tailBR"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "BASEF"; "facts_fps"; "fs_ok"; "runp"; "FUEL_T"; "zvar"; "set_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "ALU_ADD"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates"; "obindW"; "app_obj"; "axc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "FA5"; "FA6"; "T8"; "seg"; "FA1"; "FPA"; "P_fps"; "XQ1"; "XQ2"; "XW"; "bexps_eqb"; "blA"; "dropL"; "post_sub"; "x_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err.WLerrS"; "Pre_wl2"; "D"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@Stdlib.Lists.List"; "nth_error"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Fps_tailR"; "rcall_out"; "rcall"; "rc_Tm"; "sR1"; "sR2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface"; "FERR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ListCommitA"; "exts_rl_free"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface"; "fp_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates"; "unlist_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "HSE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "cells_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine"; "rom_bytes_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform";
"apply_axforms"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymBytes SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ListObj DrvPristine.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Fps_tailR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Fps_tailR.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition splitsB (e : Z) (S : sstate) : option sstate := ltac2:(tb__ "0|0|
S59S12S12S55VS;U0S11N468A1A3S12S59S12S12S55R1U1S11N448A1A3S12S59S12S12S55R1U2S11N1d0A1A3S12S59S12S12S55R1U3S11Ve;A1A3S12S59S12S12S55R1U5S11S38S77Z78A2A1A3S12S55R1U6S11S38S77Z7cA2A1A3LS5;A4LS4;A4LS3;A4LS2;A4LS1;A4").

Definition O_sufR (sufa b : Z) : sobj := ltac2:(tb__ "0|0|
S29S11Vsufa;A1S11Z0A1S11Vb;A1S6S17A1S26P6A1A5").
Definition finishB (sufa b : Z) (S6 : sstate) : sstate := ltac2:(tb__ "0|0|
S5aS7cVS6;U3P5A3S40Vsufa;Vb;A2A2").
Definition subB (lenB sufa b : Z) (Cs : sstate) : wsub := ltac2:(tb__ "0|2|
SdSfS2dS10A2M0S3G0S9S2dS10PcS1bS57S1cPaM1A1S11N1d0A1A3A4S3G0S9S2dS10PdS11VlenB;A1A4S3G0S9S2dS10PeS11Vsufa;A1A4S3G0S9S2dS10PfS11Vb;A1A4S6G0A1A3A3A3A3S88G1VCs;S30S6bA1A3A3").

Definition obj_far (lo0 hi0 : Z) (o : sobj) : bool := ltac2:(tb__ "0|14|
S10S2Lx;M0S1eVo;A1S2cG0S22Vo;A1M1S2cG0S21Vo;A1M2S2cS0S0S0S0S39R3Z0M3A2S37G3R2A2A2S37R2R1A2M4A2S37R1S85A2A2SbS37R1Vlo0;A2S37Vhi0;R2A2A2A2Lh;S2dS4Li;M5S56S10S10S4Lb;La;M6Lop;M7G7S58G6Lop;M8G8S2S2eS10S4La;Lw;Lsgn;M9S2dS10S2cS4Lk;Li;MaLl0;MbX10x8Ll;G5G7G7G8G8G9S2dGaLl;McX10x8Lbz;S2dG0G1S2cG0G2S2cS0S0S0S4cR3PaMdA2S37S3cS3bZ2Z28A2A1MeR2A2MfA2G4A2S37R1G3A2A2Lh;G5G7G7G8G8G9GbX10x8Ll;G5G7G7G8G8G9GcX10x8Lv;S56S10S10S56S2Lop;R3S10S2La;R2S2cS4Lz;S2dS10S2Lb;R2S2cG0G1S2cG0G2S2cS0S0S0S0S0S4cR4GdA2S37GeR3A2A2S37R3G3A2A2GfA2G4A2S37S38R3R1A2G3A2A2Lh;G5S56S10S10S4Lb0;La0;M10Lop0;M11G11S58G10Lop0;M12G12S2S2eS10S4La0;Lw;Lsgn;M13GbX10x8Ll;G5G11G11G12G12G13GcX10x8Lc;S2dG0G1S2cS0S0S4cR3P12A2S4cR2P14A2A2S39R1G3A2A2Ll;G5G11G11G12G12G13GcX10x8Lv2;G11G11G12G12G13GcX10x8Lv1;G11G11G12G12G13GcX10x8S4S4S4S4S4S4S4S4S4X56xaLb;La;Lop;G7G8G8G9GcX10x8").

Definition iov01_ok (W2 : axst) (i : nat) (c : Z) : bool := ltac2:(tb__ "0|7|
S0S0S0S0S0S0S0S0S15S18S30VW2;A1M0Z11A2S11Z42A1A2S15S18G0ZaA2S11Z2A1A2A2S15S18G0ZcA2S11Z1A1A2A2S15S18G0ZbA2S1bS57S1cPaA1M1S11Vc;A1M2A3A2A2S37N1000Vc;A2A2S37S38Vc;Z10A2Z0M3A2A2S39S23G0A1Zd6760A2A2S5S1aG0A1A1A2S1S14A1S2Lx;S6eS14S19G0A1Vi;A3S14S0S0S15S1eR1A1G1A2S6fS17S32S1dG2Z8M4S11G3A1M5A3A1S1fR1A1M6A3A2S6fS17S32S1dS11S38Vc;G4A2A1G4G5A3A1G6A3A2Lob;S4X1x2A2").

Record tailB_out := TBO { tb_W : axst; tb_S6 : sstate; tb_Cs : sstate; tb_s : wsub; tb_R : list sobj; tb_T : axst; tb_W2 : axst;
                          tb_F : axst; tb_G1 : sstate; tb_G2 : sstate; tb_G2u : sstate; tb_G3 : sstate; tb_sp : wsub }.

Definition tailB_post (pre suf : list Z) (n sufa : Z) (T8 : axst) (W1 : axst) : option tailB_out := ltac2:(tb__ "0|1f|
S3aS7S2cVpre;A2A1S2cS3aS7S2cVsuf;A2A1S2cS38R2Vn;A2S2cS2S1S3eA1M0L_;M1S5S0S39S23S30VW1;A1M2A1Zd6760M3A2S4dS13S30VT8;A1A1M4S13G2A1A2A2A1SaS3eA1M5S1S2fA1G0Lx;M6S8eS54VW1;S4fA2S65A2S2fG1S5S0S70S16S16S6fS16S2aR1A1S2bS30R2A1M7A1A3Lf;S4fA3S4dG4S13S30R1A1M8A1M9A2A2A1G5S1S12A1G0Lx;MaS48S38N1d0MbR2A2G8A2S12S1S14A1G0Lx;McS6eS14S19R1A1MdU3MeA3S14S1S8S86A1MfA1G0Lx;S87S1fR1A1M10S11GbA1M11Z0M12S3dR4A1A4GfG1S5S0S0S0S0S0S0S0S0S0S0S0S0S66R1S67Vpre;Vn;S6S2cA1A3A2S5S6dP5M13R3A2A1A2S5S6dP6M14R3A2A1A2S27S20R2A1M15A1A2S5S28G15A1A1A2S15S22R2A1G11A2A2S15S21R2A1S11S38GbR5A2A1A2A2S7eG13S19R3A1M16A2A2S7eG14G16A2A2S70S14S47Vsufa;S38Vsufa;R6A2M17A2G16A3A2S8dS82Vsufa;S80S2cS90Q8M18A1S8fG18A1Vsuf;A4A3A2S37G17S3bZ2Z20A2A2A2S37G12Vsufa;A2A2A1G5S45Vsufa;R6R3A3S12S33R5R1A2S2fS49R7Vsufa;R8R2A4S78G1S5S6aR7S13R3A1M19A2A1G5S1S8S14A1M1aA1G0Lx;S8aR2S6bR1A3G1aG1S5S0S0S0S0S0S0S89R3S6bR2R1S3S2fS6cS6S2fA1A3A5S24R4A1A2S15S79R2PdA2S11R9A1A2A2S15S79R2PfA2S11RaA1A2A2S4cS13R4A1S13S30R8A1A1M1bA2A2S4cS13S7cR7GeG13A3A1G1bA2A2S4cS13R7A1G1bA2M1cA2A1G5S8bR2S6bS6cR3R1A5S2fS7bS4eR1A2S2fG1SbS1aG8A1S5S4dS76S13G7A1A2A1A2G5G6S5fS52R1G3A3S2fG1S5S0S0S46R1U5N238A3S4dS13S30R3A1A1G9A2A2S15S31R1A1S11S81A1M1dA2A2A1G5S8cR1S11G12A1A2S2fG6S5fS52R1S83A3S2fS7bS4fR1A2S2fGaS7dG8S63A2S12GcS6eS14GdU14A3S14G1S5S0S36R1S40Vsufa;R12A2A2S7fS7S14S19R2A1A2U15A2A2A1G5S68R2A1S12GcS6eS14GdU1M1eA3S14G1S5S0S34S20R1A1S25G13A1A2S7fS7S17G10A2U0A2A2A1G5S84R2G1eA2S12G1S5S24R1A1A1G5GaS7dR1S64A2S12S69R1A1S78G1S0S0S0S0S0S0S0S0S0S35S5bR2A1S62R1A3S7aR1S76A2A2S5S6dG13R2A2A1A2S5S6dG14R2A2A1A2S15S31R8A1G1dA2A2S4dS76G1bA2A2S4dS13S30RbA1A1G1bA2A2G1cA2S4cG19G1bA2A2S4cS13R2A1G1bA2A2ScS3eS43R15R14R11RfReRdRbR9R7R5R3R2R1AdA2G5X2x2Tsp;LG3;G5X1x2X2x2TG2u;X2x2Lob1;G5X1x2TG2;X2x2Lob2;G5X1x2LG1;G5X1x2TF;LF0;G5X1x2TW2a;X2x2LW2;G5X1x2X2x2TTf;TT;X2x2LR;G5X1x2X2x2Ts;TC;TCs;X2x2Lbl;G5X1x2Lo8;G5X1x2LS6;G5X1x2X2x2LW;G5X1x2X2x2TlenB;Tb;Ta;").

Definition FSB (n r : Z) (T7 : axst) : list (list sprop) := ltac2:(tb__ "0|1|
SdS8S16A1M0S61Vn;VT7;A2S3G0S5dS53VT7;A1Vn;Vr;A3S3G0S4eS6G0A1A3A3A3").
Definition tailB (pre suf : list Z) (n r sufa : Z) (cls : list sprop) (T7 : axst) : option tailB_out := ltac2:(tb__ "0|5|
S5eS3aS7S2cVpre;A2A1Vn;Vr;Vcls;VT7;A5S2fS2S1S3eA1M0L_;S5S0S50S42Vn;Vr;VT7;A3M1S30R1A1M2A2S50S3S8S16A1M3S4fS6G3A1A3G2A2A2A1SaS3eA1M4S1S2fA1G0Lx;S51G1R1A2S2fS41Vpre;Vsuf;Vn;Vsufa;R2R1A6LW1;G4X1x2X2x2TT8;").
Definition tailB_ok (pre suf : list Z) (n r sufa : Z) (cls : list sprop) (T7 : axst) : bool := ltac2:(tb__ "0|0|
S1S3eA1S2Lx;S4aVpre;Vsuf;Vn;Vr;Vsufa;Vcls;VT7;A7S3eSeLt;S4X1x2").

Record tailBR_out := TBRO { tbr_M4 : axst; tbr_c1 : rcall_out; tbr_c2 : rcall_out; tbr_W1 : axst; tbr_o : tailB_out }.
Definition tailBR (pre suf : list Z) (n r sufa : Z) (cls : list sprop) (T7 : axst) : option tailBR_out := ltac2:(tb__ "0|b|
S3aS7S2cVpre;A2A1S2cS5eR1Vn;Vr;Vcls;VT7;A5S2fS53VT7;A1S2dS2S1S3fA1M0L_;M1S5S50S3S8S16A1M2S60R1Vn;A2M3S3G2S4eS3G2S5cR1Vn;A2S3G2S5dR1Vn;Vr;A3S3G2S4fS6G2A1M4A3A3A3A3A3S30R2A1A2A1SaS3fA1M5S1S2fA1G0Lx;M6S51S3G2G3S3G2S4eS3G2S4eS3G2S4eG4A3M7A3A3A3R2A2S2fG1SbS1aS30R1A1M8A1S5S4dS13S30R3A1A1S13G8A1A2A1A2G5S1S71A1G0Lx;M9S72S5cR2Vn;A2S74R4A1R1A3S71G9S72S5cR3Vn;A2S75R5A1S73R1A1MaA3S71G6S51S3G2S5cR4Vn;A2S3G2S5dR4Vn;Vr;A3G7A3A3GaA2S2fS1S3eA1G0Lx;S41Vpre;Vsuf;Vn;Vsufa;R6R1A6S3eScS3fS44R5R4R3R2R1A5A2Lo;G5X1x2LW1;G5X1x2Lc2;G5X1x2Lc1;G5X1x2X2x2LM4;G5X1x2X2x2Tv;TT8;Ta;").
Definition tailBR_ok (pre suf : list Z) (n r sufa : Z) (cls : list sprop) (T7 : axst) : bool := ltac2:(tb__ "0|0|
S1S3fA1S2Lx;S4bVpre;Vsuf;Vn;Vr;Vsufa;Vcls;VT7;A7S3fSeLt;S4X1x2").

Definition SUFA_C : Z := FMT_COPEN + 19.
Definition SUFA_U : Z := FMT_USAGE + 9.
End Fps_tailBdefs.

(* [comment removed for export] *)
Module Fps_prefix.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "holds"; "rw"; "sprop_below"; "agree_below"; "ss_next"; "SVar"; "eval"; "ss_lenient"; "SPEq"; "ss_facts"; "rl"; "sv"; "SAlu"; "SLit"; "sobj"; "sprop_eqb"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "sub"; "modulo"; "lt"; "to_nat"; "pow"; "land"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "length"; "nat"; "app"; "cons"; "false"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@"; "Pre"; "T7b"; "T7s"; "T3"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "facts_fps"; "zvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "Posts_fps"; "T8"; "small_facts"; "tailA_ok"; "ALIGN"; "aln"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA"; "MSGb"; "Kf"; "Kwr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsB"; "factsS"; "sX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen"; "FirstNul"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "FdChannel"; "fd_lookup"; "m_fds"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nq.Fps_tailCdefs"; "T8C"; "big_facts_C"; "tailC_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nx.Fps_prefix.FPS_FMT"; "T3"; "T5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nx.Fps_prefix.FpsSum.SumA.Rho"; "tail_stmt"; "tail_stmt_ex"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ns.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Icpt_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Icpt_strnlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_run OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_facts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nq.Fps_tailCdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Fps_tailC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Lemma land3 : ltac2:(tb__ "0|0|
S4bS1bZ0R1A2S13S4bS22R2Z3A2S1eR2Z4A2A3F_;Fz;").
Proof. intros z Hz. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma and3_val : ltac2:(tb__ "0|1|
S2SeS13S4bS25Q40M0S9R2SfS62R1S10Z3A1A3A2A2S1eS25G0S9R2R1A2A2Z4A2A3Fe;Frho;").
Proof.
  intros rho e. cbn [eval]. unfold alu64, alu. rewrite bv_and_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 3) with 3. apply land3. apply (proj1 (urange _)).
Qed.
Lemma holds_aln : ltac2:(tb__ "0|2|
S2S4bS14S1bZ0M0R1A2S1fR1Z8A2A2S1bS25Q40M1S9R3S4eA2A2S21Z2Z3eA2A2S15S3R4S3eR3A1A2S13S4bS1eS1cS25G1S9R4S4eA2A2R3A2Z4A2G0A3A2F_;F_;Fk;Frho;").
Proof.
  intros rho k Hk HsX. unfold aln. cbn [holds branch_taken]. unfold bv_eqb.
  assert (E : bv_unsigned (eval rho (if k =? 0 then sX else SAlu ALU_ADD sX (SLit k))) = bv_unsigned (eval rho sX) + k).
  { destruct (Z.eqb_spec k 0) as [->|Hk0]; [lia|]. pose proof (urange (eval rho sX)). rewrite (U_addc rho sX k (bv_unsigned (eval rho sX)) eq_refl); lia. }
  rewrite and3_val, E, (U_lit64 rho 0) by lia. rewrite Z.eqb_eq. tauto.
Qed.
Lemma ALIGN_holds : ltac2:(tb__ "0|1|
S2S1bS25Q40M0S9R1S4eA2A2S21Z2Z3eA2A2S35S1S3R2A1S3dS1eS25G0S9R2S4eA2A2Z4A2A1A3F_;Frho;").
Proof.
  intros rho HsX. set (x := bv_unsigned (eval rho sX)) in *. pose proof (Z.mod_pos_bound x 4 ltac:(lia)) as Hr.
  assert (Hyes : forall k, 0 <= k < 8 -> (x + k) mod 4 = 0 -> holds rho (aln k)) by (intros k Hk E; apply (proj2 (holds_aln rho k Hk HsX)); exact E).
  assert (Hno : forall k, 0 <= k < 8 -> (x + k) mod 4 <> 0 -> holds rho (SPNot (aln k))) by (intros k Hk E; cbn [holds]; intros H; apply (proj1 (holds_aln rho k Hk HsX)) in H; exact (E H)).
  assert (M : forall k, (x + k) mod 4 = (x mod 4 + k) mod 4) by (intros k; rewrite Z.add_mod_idemp_l by lia; reflexivity).
  unfold ALIGN.
  destruct (Z.eqb_spec (x mod 4) 0) as [E0|E0].
  { constructor; [|constructor]. apply Hyes; [lia|]. rewrite M, E0. reflexivity. }
  destruct (Z.eqb_spec (x mod 4) 1) as [E1|E1].
  { constructor; [apply Hno; [lia|]; rewrite M, E1; cbn; lia|]. constructor; [apply Hno; [lia|]; rewrite M, E1; cbn; lia|].
    constructor; [apply Hno; [lia|]; rewrite M, E1; cbn; lia|]. constructor; [|constructor]. apply Hyes; [lia|]. rewrite M, E1. reflexivity. }
  destruct (Z.eqb_spec (x mod 4) 2) as [E2|E2].
  { constructor; [apply Hno; [lia|]; rewrite M, E2; cbn; lia|]. constructor; [apply Hno; [lia|]; rewrite M, E2; cbn; lia|].
    constructor; [|constructor]. apply Hyes; [lia|]. rewrite M, E2. reflexivity. }
  assert (E3 : x mod 4 = 3) by lia.
  constructor; [apply Hno; [lia|]; rewrite M, E3; cbn; lia|]. constructor; [|constructor]. apply Hyes; [lia|]. rewrite M, E3. reflexivity.
Qed.

Lemma FirstNul_callsub : ltac2:(tb__ "0|1|
S65S2S26S11A1S61S13SeS66R4P10M0A2S8G0A1A3S4fR4A1S4fS64S63R5R4R3A3R6A2A1F_;F_;Fms;FR;Frhox;Fs;").
Proof.
  intros s rhox R ms S16 [H0 H1]. unfold FirstNul.
  change (rw (rho_sub (rho_absorb rhox R ms) s) 16) with (eval (rho_absorb rhox R ms) (wsub_get s 16)). rewrite S16.
  cbn [eval rw rl rho_sub rho_absorb]. split; assumption.
Qed.

Lemma fb_facts : ltac2:(tb__ "0|0|
S13S27S48S1S5S30A1S37A3S28A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma forallb_sprop_below_le : ltac2:(tb__ "0|0|
S4aS4aS26S1A1S13S27S48S1S5R3A1R1A3S28A3S56R4R3A2S13S27S48S1S5R4A1R3A3S28A3F_;F_;FF;Fm;Fn;").
Proof.
  intros n m F H Hle. apply forallb_forall. intros p Hp. apply (sprop_below_mono n); [exact Hle | exact (proj1 (forallb_forall _ _) H p Hp)].
Qed.
Lemma fb_factsS : ltac2:(tb__ "0|0|
S13S27S48S1S5P8dA1S2bS1S4dS37A3A3S28A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fb_factsB : ltac2:(tb__ "0|0|
S13S27S48S1S5P8dA1S2bS1S4cS37A3A3S28A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fb_factsB' : ltac2:(tb__ "0|0|
S13S27S48S1S5Pb5A1S2cS1SbS8P8cA1S8P10A1A2S2bS1S4cS37A3A3A3S28A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Module FpsSum.

Section SumA.

Variables Pre E1 E2 T3 E6s E6sS T7s E4 E4S T5 E6b E6bS T7b : axst.
Variables s_isl s_sis s_rip s_sib : wsub.
Variables R_isl R_sis R_rip R_sib : list sobj.
Definition T3S : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA.ax_add_facts (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st.factsS ++ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre.facts_fps)%list T3.
Definition T3B : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA.ax_add_facts (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st.factsB ++ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre.facts_fps)%list T3.
Definition T5F : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA.ax_add_facts (SPEq (SVar 140) (SVar 16) :: OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st.factsB ++ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre.facts_fps)%list T5.
Hypothesis run1 : sym_runA segs 2000 CUTS_FPS Pre true = Some [mkLeafA E1 RsCut].
Hypothesis run2 : sym_runA segs 3000 CUTS_FPS E1 true = Some [mkLeafA E2 RsCut].
Hypothesis efr_isl : entails_frA E2 Pre_isl s_isl = Some R_isl.
Hypothesis chk_isl : call_checkA E2 Pre_isl s_isl R_isl (map la_state Posts_isl) = true.
Hypothesis imp_isl : import_postA s_isl Pre_isl P_isl E2 R_isl = T3.
Hypothesis run3s : runp FSS T3S = Some E6s.
Hypothesis fsS : fs_ok FSS (ax_S T3S) = true.
Hypothesis xf6s : apply_axforms E6s [AXSplit 1 (SLit (-1024))] = Some E6sS.
Hypothesis efr_sis : entails_frA E6sS Pre_si s_sis = Some R_sis.
Hypothesis chk_sis : call_checkA E6sS Pre_si s_sis R_sis (map la_state Posts_si) = true.
Hypothesis imp_sis : import_postA s_sis Pre_si P_si E6sS R_sis = T7s.
Hypothesis run3b : sym_runA segs 3000 CUTS_FPS T3B true = Some [mkLeafA E4 RsCut].
Hypothesis split4 : obindW (split_obj_at (ax_S E4) 1 (SLit (-2352))) (fun S1 => split_obj_at S1 1 (SLit (-2432))) = Some (ax_S E4S).
Hypothesis xs4 : ax_setS E4 (ax_S E4S) = E4S.
Hypothesis efr_rip : entails_frA E4S Pre_rip s_rip = Some R_rip.
Hypothesis chk_rip : call_checkA E4S Pre_rip s_rip R_rip (map la_state Posts_rip) = true.
Hypothesis imp_rip : import_postA s_rip Pre_rip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.P_ret E4S R_rip = T5.
Hypothesis run5 : runp FSB T5F = Some E6b.
Hypothesis fsB : fs_ok FSB (ax_S T5F) = true.
Hypothesis xf6b : apply_axforms E6b XF6 = Some E6bS.
Hypothesis efr_sib : entails_frA E6bS Pre_si s_sib = Some R_sib.
Hypothesis chk_sib : call_checkA E6bS Pre_si s_sib R_sib (map la_state Posts_si) = true.
Hypothesis imp_sib : import_postA s_sib Pre_si P_si E6bS R_sib = T7b.
Hypothesis shapes :
  ss_lenient (ax_S Pre) = false /\ ss_next (ax_S Pre) = NF /\ ss_next (ax_S E1) = NF /\ ss_lenient (ax_S E1) = false /\ ss_pc (ax_S E1) = isl_entry
  /\ ss_next (ax_S E2) = NF /\ wsub_get s_isl 16 = SVar 16 /\ wsub_get s_isl 12 = sX
  /\ ss_next (ax_S T3) = 141%positive /\ existsb (sprop_eqb (SPEq (SVar 140) (SVar 16))) (ss_facts (ax_S T3)) = true
  /\ ss_lenient (ax_S T3S) = false /\ ss_lenient (ax_S T3B) = false
  /\ ss_next (ax_S E6s) = ss_next (ax_S E6sS) /\ (141 <=? ss_next (ax_S E6s))%positive = true /\ wsub_get s_sis 16 = SVar 16
  /\ ss_next (ax_S E4) = ss_next (ax_S E4S) /\ (141 <=? ss_next (ax_S E4))%positive = true
  /\ ss_next (ax_S T5) = (ss_next (ax_S E4) + 40)%positive /\ ss_lenient (ax_S T5F) = false
  /\ ss_next (ax_S E6b) = ss_next (ax_S E6bS) /\ (ss_next (ax_S T5) <=? ss_next (ax_S E6b))%positive = true /\ wsub_get s_sib 16 = SVar 16
  /\ zvar T7s = (ss_next (ax_S E6s) + 40)%positive /\ ss_next (ax_S T7s) = (ss_next (ax_S E6s) + 41)%positive
  /\ zvar T7b = (ss_next (ax_S E6b) + 40)%positive /\ ss_next (ax_S T7b) = (ss_next (ax_S E6b) + 41)%positive
  /\ existsb (sprop_eqb (SPEq (SVar (zvar T7s)) (SVar 16))) (ss_facts (ax_S T7s)) = true
  /\ existsb (sprop_eqb (SPEq (SVar (zvar T7b)) (SVar 16))) (ss_facts (ax_S T7b)) = true.
Hypothesis Pre_facts : ss_facts (ax_S Pre) = facts_fps.
Hypothesis Pre_str : nth_error (ss_objs (ax_S Pre)) 1 = Some O_strS.
Hypothesis lenT7 : ss_lenient (ax_S T7s) = false /\ ss_lenient (ax_S T7b) = false.

Variable ok : world -> Prop.
Variable J0 : jpredA.
Variables pre suf : list Z.
Hypothesis Hpre1 : (1 <= length pre)%nat.
Let a : Z := Z.of_nat (length pre).
Let b : Z := Z.of_nat (length suf).
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd2 : ltac2:(tb__ "0|0|
S2S26S24Q40A1A1S26S51A1S50VJ0;R4R3R2R1A4S13S2fS52A1S54S55R2A1S5cA2S2eS52S53S5cA1A2A3F_;Fmd;Ftr;Ft;Fr;").

Section Rho.
Variable rho : valuation.
Variable tp : list word.
Hypothesis HFN : FirstNul rho.
Let n : Z := bv_unsigned (rw rho 16).
Let str : list byte := ltac2:(tb__ "0|0|
S36S24Q8A1S20Vn;A1SdVrho;P3A2A3").
Let rA : Z := ltac2:(tb__ "0|0|
S1eS25Q40S9Vrho;S4eA2A2Z4A2").
Let Kwr : ltac2:(tb__ "0|0|
S2aS18Fk;") := ltac2:(tb__ "0|0|
S41VJ0;Vpre;Vsuf;Vstr;A4").
Let Kf : ltac2:(tb__ "0|0|
S2aS18Fk;") := ltac2:(tb__ "0|0|
S40VJ0;Vpre;Vsuf;Vstr;Vrho;Vtp;A6").
Hypothesis HokK : ltac2:(tb__ "0|0|
S2aS19S0Vok;VKwr;R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S2aS67S0Vok;VKwr;R1A1A3Fk;").

Lemma str_len_of_SPA : ltac2:(tb__ "0|0|
S18S44S16S0R2S31Vrho;Vtp;R1A6S13S2aS29S24Q8A1Vstr;A2S20Vn;A1A3F_;Fw;FJ;").
Proof.
  intros J w [(Hsm & _) _].
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  pose proof (proj1 (Forall_forall _ _) Hall _ (nth_error_In _ _ Pre_str)) as Ho.
  destruct Ho as (_ & _ & _ & _ & Hinv). cbn [ob_dflt O_strS dflt_inv ob_lo ob_hi] in Hinv.
  unfold obj_lo_of, obj_hi_of, O_strS in Hinv. cbn [ob_lo ob_hi] in Hinv. rewrite soff_lit_small in Hinv by lia.
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF. rewrite Pre_facts in HF. pose proof (proj2 (proj1 (Forall_app _ _ _) HF)) as HS.
  destruct (str_factsZ rho HS) as (Z1 & Z2 & _). pose proof (urange (rw rho 17)) as R17. pose proof (urange (rw rho 16)) as R16.
  assert (Hhi : soff rho (SVar 17) = bv_unsigned (rw rho 17)).
  { unfold soff. cbn [eval]. apply signed_small. lia. }
  rewrite Hhi in Hinv. unfold str, n. rewrite length_firstn. lia.
Qed.

Lemma Kf_inv : ltac2:(tb__ "0|0|
S2aS2S2S26S24Q40A1A1S26S51A1S50VKf;R6R5R3R2R1A5VKf;R7R5R4R3R2A5F_;Fmd;Ftr;Ft;Fr2;Fr1;Fk;").
Proof. intros k r1 r2 t tr md H. exact H. Qed.
Lemma Kf_tp : ltac2:(tb__ "0|1|
S2aS2S26S24Q40A1A1M0S26S51A1S50VKf;R5R4R3R2R1A5S13G0R4Vtp;A3F_;Fmd;Ftr;Ft;Fr1;Fk;").
Proof. intros k r1 t tr md [H _]. exact H. Qed.
Lemma J0_Kf0 : ltac2:(tb__ "0|0|
S26S51A1S50VJ0;Vrho;Vtp;R2R1A4VKf;U0Vrho;Vtp;R3R2A5F_;Fmd;Ft;").
Proof. intros t md HJ. split; [reflexivity|]. exists t. split; [exact HJ|]. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.EVS. cbn. rewrite app_nil_r. reflexivity. Qed.

Let Jc : jpredA := Kf 0.
Lemma HJst : ltac2:(tb__ "0|0|
S4aS1aS0R1VJc;A3Flvl;"). Proof. intros lvl. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0 lvl). Qed.
Lemma HJok : ltac2:(tb__ "0|0|
S19S0Vok;VJc;A3"). Proof. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_okK ok J0 pre suf str HokK rho tp 0). Qed.
Lemma HJinv : ltac2:(tb__ "0|0|
S2S2S26S24Q40A1A1S26S51A1S50VJc;R5R3R2R1A4VJc;R5R4R3R2A4F_;Fmd;Ftr;Ft;Fr2;Fr1;"). Proof. intros r1 r2 t tr md H. exact H. Qed.
Lemma HJtp : ltac2:(tb__ "0|1|
S2S26S24Q40A1A1M0S26S51A1S50VJc;R4R3R2R1A4S13G0R4Vtp;A3F_;Fmd;Ftr;Ft;Fr1;"). Proof. intros r1 t tr md [H _]. exact H. Qed.

Definition Jn : jpredA := ltac2:(tb__ "0|0|
S2S26S24Q40A1A1S26S51A1S50S14VJc;R4R3R2R1A4S4fR4A1A2Lmd;Ltr;Lt;Lr;").
Lemma Jn_stable : stableA segs NF Jn.
Proof.
  intros r r' t tr md md' Hag Hme [HJ HF]. split; [eapply HJst; eauto|]. eapply FirstNul_agree; [| exact Hag | exact HF]. reflexivity.
Qed.
Lemma Jn_okf : ok_frameA segs ok Jn.
Proof. intros r t tr ms md msv' [HJ _]. eapply HJok; eauto. Qed.

Lemma prefix_T3 : ltac2:(tb__ "0|0|
S45S4fVrho;A1S2S6S30Vrho;R1A3S13S24Q40A1S4R2P8cA2S4R2P10A2A3S35S1S3R3A1S37A3S43S0Vok;S16S0VJc;S34R4Vtp;A5R6A4F_;F_;F_;Frho3;S43S0Vok;S16S0VJc;S31Vrho;Vtp;A5R3A4F_;F_;FQ;").
Proof.
  intros Q _ Hk.
  destruct shapes as (HlP & HnP & HnE1 & HlE1 & _ & HnE2 & S16 & S12 & HnT3 & Hf140 & _).
  apply (triple_pre ok _ (Forall (holds rho) facts_fps)); [intros w [Hsm _]; rewrite <- Pre_facts; exact (smatchA_facts segs rho tp Pre w Hsm) | intros HF0].
  eapply (runA_tr segs ok 2000 CUTS_FPS Pre _ Jc rho tp); [exact run1 | exact HlP | exact HJok | apply HJst |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  eapply (runA_tr segs ok 3000 CUTS_FPS E1 _ Jc rho1 tp); [exact run2 | exact HlE1 | exact HJok | apply HJst |].
  intros L rho2 [<-|[]] Hag2. cbn [la_state]. rewrite HnE1 in Hag2.
  pose proof (agree_below_trans NF _ _ _ Hag1 Hag2) as Hag02.
  pose proof (FirstNul_agree NF rho rho2 ltac:(reflexivity) Hag02 HFN) as HFN2.
  apply (call_soundA segs ok Jc Jn Jn Jc E2 Pre_isl s_isl R_isl Posts_isl _ rho2 tp efr_isl chk_isl).
  - intros rhoc tpc. apply (triple_pre ok _ (FirstNul rhoc)); [intros w [_ [_ H]]; exact H | intros HFNc].
    exact (istrlen_sum ok Jn rhoc tpc Jn_okf Jn_stable HFNc).
  - intros tr ms md Hsm HJ. split; [eapply HJinv; exact HJ | apply (FirstNul_callsub s_isl); [exact S16 | exact HFN2]].
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [HJ' _]. eapply HJinv; exact HJ'.
  - intros L rho3 tpL [<-|[]] Hag3. cbn [la_state]. rewrite imp_isl. rewrite HnE2 in Hag3.
    apply (triple_pre ok _ (tpL = tp /\ Forall (holds rho3) (ss_facts (ax_S T3))));
      [intros w [Hsm HJ]; split; [exact (HJtp _ _ _ _ HJ) | exact (smatchA_facts segs _ _ _ w Hsm)] | intros [-> HF3]].
    apply Hk.
    + eapply agree_below_trans; [exact Hag02 | exact Hag3].
    + apply existsb_exists in Hf140 as (q & Hq & Eq). apply sprop_eqb_sound in Eq. subst q. exact (proj1 (Forall_forall _ _) HF3 _ Hq).
    + apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree NF rho rho3 p (agree_below_trans NF _ _ _ Hag02 Hag3) (proj1 (forallb_forall _ _) fb_facts p Hp))).
      exact (proj1 (Forall_forall _ _) HF0 p Hp).
Qed.

Lemma prefix_S : ltac2:(tb__ "0|2|
S45S4fVrho;A1S1bS1cS25Q40M0S4Vrho;P10M1A2A2Z1A2Z40A2S2S6S30Vrho;R1A3S35S1S3R2A1S37A3S13S24G0A1S4R3P8cA2S4R3G1A2A3S43S0Vok;S16S0VJc;S33R4Vtp;A5R7A4F_;F_;F_;Frho7;S43S0Vok;S16S0VJc;S31Vrho;Vtp;A5R4A4F_;F_;F_;FQ;").
Proof.
  intros Q _ HzS Hk.
  destruct shapes as (HlP & HnP & HnE1 & HlE1 & _ & HnE2 & S16 & S12 & HnT3 & Hf140 & HlS & HlB & HnE6s & HgeE6s & S16s & _).
  apply prefix_T3; [exact HFN|]. intros rho3 Hag3 H140 HF3.
  assert (Hz3 : rw rho3 16 = rw rho 16) by (destruct Hag3 as (A & _ & _); symmetry; apply A; reflexivity).
  assert (HFS : Forall (holds rho3) (factsS ++ facts_fps)).
  { apply Forall_app. split; [|exact HF3]. unfold factsS. constructor; [apply (GEU65_S' rho3 H140); rewrite Hz3; lia|].
    apply (post_facts_hold' rho3); [apply Forall_app in HF3 as [_ HS]; exact HS | exact H140]. }
  eapply triple_conseq with (P := SPA segs Jc T3S rho3 tp);
    [intros w [Hsm HJ]; split; [apply smatchA_add_facts; [exact Hsm | exact HFS | rewrite HnT3; exact fb_factsS] | exact HJ] | intros w Hw; exact Hw |].
  apply (triple_pre ok _ (FsHold rho3 FSS /\ FsBelow (ss_next (ax_S T3S)) FSS = true)); [intros w Hw; exact (fs_ok_sound Jc FSS T3S rho3 tp w fsS Hw) | intros [HFh HFb]].
  eapply (runp_tr ok Jc HJst FSS T3S E6s rho3 tp); [exact run3s | exact HlS | exact HJok | exact HFh | exact HFb |].
  intros rho6 Hag6.
  assert (Hn3S : ss_next (ax_S T3S) = 141%positive) by (unfold T3S, ax_add_facts, add_facts; destruct T3 as [S3 X3 b3]; cbn; cbn in HnT3; exact HnT3).
  rewrite Hn3S in Hag6. apply Pos.leb_le in HgeE6s.
  eapply triple_conseq with (P := SPA segs Jc E6sS rho6 tp); [intros w Hw; exact (SPA_axforms segs _ _ rho6 E6s E6sS tp w xf6s Hw) | intros w Hw; exact Hw |].
  pose proof (agree_below_trans NF _ _ _ Hag3 (agree_below_le 141 NF _ _ ltac:(unfold NF; lia) Hag6)) as Hag06.
  pose proof (FirstNul_agree NF rho rho6 ltac:(reflexivity) Hag06 HFN) as HFN6.
  apply (call_soundA segs ok Jc Jn Jn Jc E6sS Pre_si s_sis R_sis Posts_si _ rho6 tp efr_sis chk_sis).
  - intros rhoc tpc. apply (triple_pre ok _ (FirstNul rhoc)); [intros w [_ [_ H]]; exact H | intros HFNc].
    exact (si_sum ok Jn Jn_okf Jn_stable rhoc tpc HFNc).
  - intros tr ms md Hsm HJ. split; [eapply HJinv; exact HJ | apply (FirstNul_callsub s_sis); [exact S16s | exact HFN6]].
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [HJ' _]. eapply HJinv; exact HJ'.
  - intros L rho7 tpL [<-|[]] Hag7. cbn [la_state]. rewrite imp_sis. rewrite <- HnE6s in Hag7.
    apply (triple_pre ok _ (tpL = tp)); [intros w [Hsm HJ]; exact (HJtp _ _ _ _ HJ) | intros ->].
    pose proof (agree_below_trans NF _ _ _ Hag06 (agree_below_le (ss_next (ax_S E6s)) NF _ _ ltac:(unfold NF; lia) Hag7)) as Hag07.
    apply Hk; [exact Hag07| |].
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree NF rho3 rho7 p (agree_below_trans NF _ _ _ (agree_below_le 141 NF _ _ ltac:(unfold NF; lia) Hag6) (agree_below_le (ss_next (ax_S E6s)) NF _ _ ltac:(unfold NF; lia) Hag7))
               (proj1 (forallb_forall _ _) fb_facts p Hp))).
      exact (proj1 (Forall_forall _ _) HF3 p Hp). }
    destruct Hag6 as (A6 & _ & _). destruct Hag7 as (A7 & _ & _).
    rewrite <- (A7 140%positive) by lia. rewrite <- (A7 16%positive) by lia. rewrite <- (A6 140%positive) by lia. rewrite <- (A6 16%positive) by lia. exact H140.
Qed.

Lemma prefix_B : ltac2:(tb__ "0|2|
S45S4fVrho;A1S1bZ41S1cS25Q40M0S4Vrho;P10M1A2A2Z1A2A2S2S6S30Vrho;R1A3S35S1S3R2A1S37A3S13S24G0A1S4R3P8cA2S4R3G1A2A3S43S0Vok;S16S0VJc;S32R4Vtp;A5R7A4F_;F_;F_;Frho7;S43S0Vok;S16S0VJc;S31Vrho;Vtp;A5R4A4F_;F_;F_;FQ;").
Proof.
  intros Q _ HzB Hk.
  destruct shapes as (HlP & HnP & HnE1 & HlE1 & _ & HnE2 & S16 & S12 & HnT3 & Hf140 & HlS & HlB & HnE6s & HgeE6s & S16s
                      & HnE4 & HgeE4 & HnT5 & HlT5F & HnE6b & HgeE6b & S16b & _).
  apply prefix_T3; [exact HFN|]. intros rho3 Hag3 H140 HF3.
  assert (Hz3 : rw rho3 16 = rw rho 16) by (destruct Hag3 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HF3)) as HS3.
  assert (HFB : Forall (holds rho3) (factsB ++ facts_fps)).
  { apply Forall_app. split; [|exact HF3]. unfold factsB. constructor; [apply (GEU65_B' rho3 HS3 H140); rewrite Hz3; lia|].
    apply Forall_app. split; [exact (post_facts_hold' rho3 HS3 H140) | apply (big_facts_hold' rho3 HS3 H140); rewrite Hz3; lia]. }
  eapply triple_conseq with (P := SPA segs Jc T3B rho3 tp);
    [intros w [Hsm HJ]; split; [apply smatchA_add_facts; [exact Hsm | exact HFB | rewrite HnT3; exact fb_factsB] | exact HJ] | intros w Hw; exact Hw |].
  eapply (runA_tr segs ok 3000 CUTS_FPS T3B _ Jc rho3 tp); [exact run3b | exact HlB | exact HJok | apply HJst |].
  intros L rho4 [<-|[]] Hag4. cbn [la_state].
  assert (Hn3B : ss_next (ax_S T3B) = 141%positive) by (unfold T3B, ax_add_facts, add_facts; destruct T3 as [S3 X3 b3]; cbn; cbn in HnT3; exact HnT3).
  rewrite Hn3B in Hag4. apply Pos.leb_le in HgeE4. apply Pos.leb_le in HgeE6b.

  assert (Hsp4 : forall w, SPA segs Jc E4 rho4 tp w -> SPA segs Jc E4S rho4 tp w).
  { intros w Hw. pose proof split4 as Hs. unfold obindW in Hs.
    destruct (split_obj_at (ax_S E4) 1 (SLit (-2352))) as [S1|] eqn:E1s; [|discriminate].
    pose proof (SPA_split segs Jc rho4 E4 1 (SLit (-2352)) S1 tp w E1s Hw) as H1.
    pose proof (SPA_split segs Jc rho4 (ax_setS E4 S1) 1 (SLit (-2432)) (ax_S E4S) tp w Hs H1) as H2.
    rewrite ax_setS_setS, xs4 in H2. exact H2. }
  eapply triple_conseq with (P := SPA segs Jc E4S rho4 tp); [exact Hsp4 | intros w Hw; exact Hw |].
  apply (call_soundA segs ok Jc Jc Jc Jc E4S Pre_rip s_rip R_rip Posts_rip _ rho4 tp efr_rip chk_rip).
  - intros rhoc tpc. exact (region_sum ok Jc rhoc tpc HJok (HJst NF)).
  - intros tr ms md Hsm HJ. eapply HJinv; exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. eapply HJinv; exact HJ'.
  - intros L rho5 tpL [<-|[]] Hag5. cbn [la_state]. rewrite imp_rip. rewrite <- HnE4 in Hag5.
    apply (triple_pre ok _ (tpL = tp)); [intros w [Hsm HJ]; exact (HJtp _ _ _ _ HJ) | intros ->].
    pose proof (agree_below_trans 141 _ _ _ Hag4 (agree_below_le (ss_next (ax_S E4)) 141 _ _ HgeE4 Hag5)) as Hag35.
    assert (HFB5 : Forall (holds rho5) (SPEq (SVar 140) (SVar 16) :: factsB ++ facts_fps)).
    { apply (Forall_holds_agree 141 rho3 rho5); [exact Hag35 | exact fb_factsB' |]. constructor; [| exact HFB]. cbn [holds eval]. exact H140. }
    eapply triple_conseq with (P := SPA segs Jc T5F rho5 tp);
      [intros w [Hsm HJ]; split; [apply smatchA_add_facts; [exact Hsm | exact HFB5 | rewrite HnT5; apply (forallb_sprop_below_le 181); [exact fb_factsB' | lia]] | exact HJ] | intros w Hw; exact Hw |].
    apply (triple_pre ok _ (FsHold rho5 FSB /\ FsBelow (ss_next (ax_S T5F)) FSB = true)); [intros w Hw; exact (fs_ok_sound Jc FSB T5F rho5 tp w fsB Hw) | intros [HFh HFb]].
    eapply (runp_tr ok Jc HJst FSB T5F E6b rho5 tp); [exact run5 | exact HlT5F | exact HJok | exact HFh | exact HFb |].
    intros rho6 Hag6.
    assert (Hn5F : ss_next (ax_S T5F) = ss_next (ax_S T5)) by (unfold T5F, ax_add_facts, add_facts; destruct T5 as [S5 X5 b5]; reflexivity).
    rewrite Hn5F, HnT5 in Hag6.
    eapply triple_conseq with (P := SPA segs Jc E6bS rho6 tp); [intros w Hw; exact (SPA_axforms segs _ _ rho6 E6b E6bS tp w xf6b Hw) | intros w Hw; exact Hw |].
    pose proof (agree_below_trans NF _ _ _ Hag3 (agree_below_le 141 NF _ _ ltac:(unfold NF; lia) (agree_below_trans 141 _ _ _ Hag35 (agree_below_le (ss_next (ax_S E4) + 40)%positive 141 _ _ ltac:(lia) Hag6)))) as Hag06.
    pose proof (FirstNul_agree NF rho rho6 ltac:(reflexivity) Hag06 HFN) as HFN6.
    apply (call_soundA segs ok Jc Jn Jn Jc E6bS Pre_si s_sib R_sib Posts_si _ rho6 tp efr_sib chk_sib).
    + intros rhoc tpc. apply (triple_pre ok _ (FirstNul rhoc)); [intros w [_ [_ H]]; exact H | intros HFNc].
      exact (si_sum ok Jn Jn_okf Jn_stable rhoc tpc HFNc).
    + intros tr ms md Hsm HJ. split; [eapply HJinv; exact HJ | apply (FirstNul_callsub s_sib); [exact S16b | exact HFN6]].
    + intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [HJ' _]. eapply HJinv; exact HJ'.
    + intros L rho7 tpL [<-|[]] Hag7. cbn [la_state]. rewrite imp_sib. rewrite <- HnE6b in Hag7.
      apply (triple_pre ok _ (tpL = tp)); [intros w [Hsm HJ]; exact (HJtp _ _ _ _ HJ) | intros ->].
      assert (Hag67 : agree_below NF rho6 rho7) by (eapply (agree_below_le (ss_next (ax_S E6b)) NF); [unfold NF; lia | exact Hag7]).
      apply Hk; [eapply agree_below_trans; [exact Hag06 | exact Hag67] | |].
      { apply Forall_forall. intros p Hp.
        apply (proj1 (holds_agree NF rho3 rho7 p
                 (agree_below_trans NF _ _ _ (agree_below_le 141 NF _ _ ltac:(unfold NF; lia) (agree_below_trans 141 _ _ _ Hag35 (agree_below_le (ss_next (ax_S E4) + 40)%positive 141 _ _ ltac:(lia) Hag6))) Hag67)
                 (proj1 (forallb_forall _ _) fb_facts p Hp))).
        exact (proj1 (Forall_forall _ _) HF3 p Hp). }
      destruct Hag35 as (A35 & _ & _). destruct Hag6 as (A6 & _ & _). destruct Hag7 as (A7 & _ & _).
      rewrite <- (A7 140%positive) by lia. rewrite <- (A7 16%positive) by lia. rewrite <- (A6 140%positive) by lia. rewrite <- (A6 16%positive) by lia.
      rewrite <- (A35 140%positive) by lia. rewrite <- (A35 16%positive) by lia. exact H140.
Qed.

Lemma small_facts_hold : ltac2:(tb__ "0|0|
S2S47S26S1A1S6S30Vrho;R3A3S35S1S3R4A1ScS46R3A1A1A3S13S27S49S1S12SbS8S38R4A1A1S8P10A1A2A1ScS46R4A1A1A3S28A3S35S1S3R6A1S37A3S35S1S3R7A1R5A3S1bVn;S1dZ50Va;A2A2S35S1S3R9A1S3bVa;Vn;VrA;S38R8A1R7A5A3F_;F_;F_;F_;F_;F_;Fcls;FT7;Frho7;").
Proof.
  intros rho7 T7 cls Hag HF7 Hz HFf Hcls Hna.
  apply existsb_exists in Hz as (q & Hq & Eq). apply sprop_eqb_sound in Eq. subst q.
  pose proof (proj1 (Forall_forall _ _) HF7 _ Hq) as Ez. cbn [holds eval] in Ez.
  pose proof Hag as (A & L & _).
  assert (E16 : rw rho7 16 = rw rho 16) by (symmetry; apply A; reflexivity).
  assert (HFN7 : FirstNul rho7) by (eapply (FirstNul_agree NF); [reflexivity | exact Hag | exact HFN]).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HFf)) as HS7.
  destruct (str_factsZ rho7 HS7) as (Z1 & Z2 & Z3 & Z4 & Z5 & HsX & _). rewrite E16 in Z1.
  assert (EsX : eval rho7 sX = eval rho sX).
  { unfold sX, vXB, vXO. cbn [eval]. rewrite (A 18%positive), (A 20%positive) by reflexivity. reflexivity. }
  pose proof (urange (rw rho 16)) as R16.
  unfold small_facts. apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split; [| apply Forall_app; split; [exact Hcls | exact HFf]]]].
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (proj2 (holds_BZ rho7 (SVar (zvar T7)))). cbn [eval]. rewrite Ez. exact (proj1 HFN7).
    + apply (proj2 (holds_BZ rho7 (SLit n))). cbn [eval]. rewrite lit_unsigned, Z.mod_small by (unfold n; lia). unfold n. rewrite <- E16. exact (proj1 HFN7).
    + unfold FWSMALL. cbn [holds branch_taken eval]. unfold bv_ltu. rewrite Ez, E16, lit_unsigned, Z.mod_small by (unfold a in *; lia).
      destruct (Z.ltb_spec (80 - a) (bv_unsigned (rw rho 16))); [exfalso; unfold n, a in *; lia | reflexivity].
  - unfold ZLIT. constructor; [|constructor; [|constructor]]; cbn [holds eval]; rewrite Ez, E16, lit_unsigned, Z.mod_small by (unfold n; lia); unfold n; lia.
  - unfold rA. rewrite <- EsX. apply ALIGN_holds. exact HsX.
Qed.

Lemma small_facts_below : ltac2:(tb__ "0|0|
S4aS4aS26S1A1S56P8dR3A2S57R3R4A2S13S27S48S1S5R5A1R3A3S28A3S13S27S48S1S5R6A1S3bVa;Vn;VrA;R5R4A5A3S28A3F_;F_;F_;Fcls;Fzv;Fnx;").
Proof.
  intros nx zv cls Hnx Hzv Hcls. unfold small_facts.
  rewrite !forallb_app. rewrite Hcls, (fb_facts_le nx) by (unfold NF; lia).
  assert (Z18 : (18 <? nx)%positive = true) by (apply Pos.ltb_lt; lia).
  assert (Z20 : (20 <? nx)%positive = true) by (apply Pos.ltb_lt; lia).
  assert (Zv : (zv <? nx)%positive = true) by (apply Pos.ltb_lt; lia).
  assert (HA : forall k, sprop_below nx (aln k) = true).
  { intros k. unfold aln. destruct (k =? 0); cbn -[Pos.ltb]; rewrite ?Z18, ?Z20; reflexivity. }
  assert (HAL : forallb (sprop_below nx) (ALIGN rA) = true).
  { unfold ALIGN. destruct (rA =? 0); [|destruct (rA =? 1); [|destruct (rA =? 2)]]; cbn [forallb sprop_below]; rewrite !HA; reflexivity. }
  rewrite HAL. cbn -[Pos.ltb]. rewrite ?Z18, ?Z20, ?Zv. reflexivity.
Qed.

Lemma T8_shape : ltac2:(tb__ "0|3|
S26S1A1S47S14S13S27SaS46S3aVa;Vn;VrA;R2R1A5A1M0A1SaS46R1A1M1A1A3S14S13S4aS7G0A1S7G1A1A3S2S26S24Q40A1A1S44S35S1S3R3A1S3bVa;Vn;VrA;S38R4A1R5A5A3S13S27S48S1S5S7S46R5A1A1A1S3bVa;Vn;VrA;S38R5A1R6A5A3S28A3S16S0VKf;U0A1M2R6R5R4R3A6S16S0G2S3aVa;Vn;VrA;R8R7A5R6R5R4A6F_;F_;F_;Fw;Ftpx;Frho7;A2A2FT7;Fcls;").
Proof.
  intros cls T7. unfold T8, ax_add_facts, add_facts. destruct T7 as [S7 X7 b7]. cbn. split; [reflexivity|]. split; [reflexivity|].
  intros rho7 tpx w HF Hb Hsp. exact (SPA_add_facts _ rho7 tpx _ {| ax_S := S7; ax_X := X7; ax_base := b7 |} w HF Hb Hsp).
Qed.

Theorem fpsA_sound_S : ltac2:(tb__ "0|1|
S26S26S1A1A1S1bS1cVn;Z1A2Z40A2S1bS1cS1cVa;Vn;A2Vb;A2M0Z50A2S13S27S3cR3Vpre;Vsuf;Vn;G0S3aVa;Vn;VrA;S4dS33A5A6S28A3S43S0Vok;S16S0VJ0;S31Vrho;Vtp;A5S17S0VKwr;S29S24Q8A1S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A4F_;F_;F_;FLFs;").
Proof.
  intros LFs HzS Hfit Hok.
  apply (triple_pre ok _ (length str = Z.to_nat n)); [intros w Hw; exact (str_len_of_SPA _ w Hw) | intros Hstr_len].
  destruct shapes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnE6s & HgeE6s & _ & _ & _ & _ & _ & _ & _ & _ & Hzv7 & Hn7 & _ & _ & Hz7 & _).
  destruct lenT7 as [Hl7 _]. apply Pos.leb_le in HgeE6s.
  unfold tailA_ok in Hok. destruct (tailA LFs pre suf n (a + n + b) (T8 a n rA factsS T7s)) as [o|] eqn:Hcert; [|discriminate]. clear Hok.
  pose proof (urange (rw rho 16)) as R16.
  apply (triple_SPA_conseq_J segs ok _ (Kf 0)); [intros t md HJ; exact (J0_Kf0 t md HJ)|].
  apply (prefix_S _ HFN HzS).
  intros rho7 Hag7 HFf H140.
  apply (triple_pre ok _ (Forall (holds rho7) (ss_facts (ax_S T7s)))); [intros w [Hsm _]; exact (smatchA_facts segs rho7 tp T7s w Hsm) | intros HF7].
  assert (E16 : rw rho7 16 = rw rho 16) by (destruct Hag7 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HFf)) as HS7.
  assert (Hcls : Forall (holds rho7) factsS).
  { unfold factsS. constructor; [apply (GEU65_S' rho7 H140); rewrite E16; unfold n in HzS; lia | exact (post_facts_hold' rho7 HS7 H140)]. }
  pose proof (small_facts_hold rho7 T7s factsS Hag7 HF7 Hz7 HFf Hcls ltac:(unfold n, a, b in *; lia)) as HSF.
  destruct (T8_shape factsS T7s) as (HlT8 & HnT8 & HT8).
  eapply triple_conseq with (P := SPA segs (Kf 0) (T8 a n rA factsS T7s) rho7 tp);
    [intros w Hw; apply (HT8 rho7 tp w HSF); [apply small_facts_below; [rewrite Hn7; lia | rewrite Hzv7, Hn7; lia | rewrite Hn7; apply (forallb_sprop_below_le 141); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | lia]] | exact Hw] | intros w Hw; exact Hw |].
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.tailA_sound ok J0 pre suf str Hst0 Hfd2 HokK HokP rho tp ltac:(rewrite Hstr_len; reflexivity)
           n (a + n + b) ltac:(rewrite Hstr_len; unfold n; lia) ltac:(unfold a, b; lia) Hfit Hpre1 LFs (T8 a n rA factsS T7s) o Hcert
           ltac:(rewrite HlT8; exact Hl7) ltac:(rewrite HnT8, Hn7; unfold NF; lia) rho7 Hag7).
Qed.

Lemma prefix_T3_ex : ltac2:(tb__ "0|0|
S44OF_;S4fVrho;A1S2S6S30Vrho;R1A3S13S24Q40A1S4R2P8cA2S4R2P10A2A3S35S1S3R3A1S37A3S42S0S16S0VJc;S34R4Vtp;A5R6A3F_;F_;F_;Frho3;S42S0S16S0VJc;S31Vrho;Vtp;A5R3A3F_;F_;FQ;").
Proof.
  intros Q _ Hk.
  destruct shapes as (HlP & HnP & HnE1 & HlE1 & _ & HnE2 & S16 & S12 & HnT3 & Hf140 & _).
  apply (etriple_pre _ (Forall (holds rho) facts_fps)); [intros w [Hsm _]; rewrite <- Pre_facts; exact (smatchA_facts segs rho tp Pre w Hsm) | intros HF0].
  eapply (erunA_tr segs 2000 CUTS_FPS Pre _ Jc rho tp); [exact run1 | exact HlP | apply HJst |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  eapply (erunA_tr segs 3000 CUTS_FPS E1 _ Jc rho1 tp); [exact run2 | exact HlE1 | apply HJst |].
  intros L rho2 [<-|[]] Hag2. cbn [la_state]. rewrite HnE1 in Hag2.
  pose proof (agree_below_trans NF _ _ _ Hag1 Hag2) as Hag02.
  pose proof (FirstNul_agree NF rho rho2 ltac:(reflexivity) Hag02 HFN) as HFN2.
  apply (call_completeA segs Jc Jn Jn Jc E2 Pre_isl s_isl R_isl Posts_isl _ rho2 tp efr_isl chk_isl).
  - intros rhoc tpc. apply (etriple_pre _ (FirstNul rhoc)); [intros w [_ [_ H]]; exact H | intros HFNc].
    exact (istrlen_sum_ex Jn rhoc tpc Jn_stable HFNc).
  - intros tr ms md Hsm HJ. split; [eapply HJinv; exact HJ | apply (FirstNul_callsub s_isl); [exact S16 | exact HFN2]].
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [HJ' _]. eapply HJinv; exact HJ'.
  - intros L rho3 tpL [<-|[]] Hag3. cbn [la_state]. rewrite imp_isl. rewrite HnE2 in Hag3.
    apply (etriple_pre _ (tpL = tp /\ Forall (holds rho3) (ss_facts (ax_S T3))));
      [intros w [Hsm HJ]; split; [exact (HJtp _ _ _ _ HJ) | exact (smatchA_facts segs _ _ _ w Hsm)] | intros [-> HF3]].
    apply Hk.
    + eapply agree_below_trans; [exact Hag02 | exact Hag3].
    + apply existsb_exists in Hf140 as (q & Hq & Eq). apply sprop_eqb_sound in Eq. subst q. exact (proj1 (Forall_forall _ _) HF3 _ Hq).
    + apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree NF rho rho3 p (agree_below_trans NF _ _ _ Hag02 Hag3) (proj1 (forallb_forall _ _) fb_facts p Hp))).
      exact (proj1 (Forall_forall _ _) HF0 p Hp).
Qed.

Lemma prefix_S_ex : ltac2:(tb__ "0|2|
S44OF_;S4fVrho;A1S1bS1cS25Q40M0S4Vrho;P10M1A2A2Z1A2Z40A2S2S6S30Vrho;R1A3S35S1S3R2A1S37A3S13S24G0A1S4R3P8cA2S4R3G1A2A3S42S0S16S0VJc;S33R4Vtp;A5R7A3F_;F_;F_;Frho7;S42S0S16S0VJc;S31Vrho;Vtp;A5R4A3F_;F_;F_;FQ;").
Proof.
  intros Q _ HzS Hk.
  destruct shapes as (HlP & HnP & HnE1 & HlE1 & _ & HnE2 & S16 & S12 & HnT3 & Hf140 & HlS & HlB & HnE6s & HgeE6s & S16s & _).
  apply prefix_T3_ex; [exact HFN|]. intros rho3 Hag3 H140 HF3.
  assert (Hz3 : rw rho3 16 = rw rho 16) by (destruct Hag3 as (A & _ & _); symmetry; apply A; reflexivity).
  assert (HFS : Forall (holds rho3) (factsS ++ facts_fps)).
  { apply Forall_app. split; [|exact HF3]. unfold factsS. constructor; [apply (GEU65_S' rho3 H140); rewrite Hz3; lia|].
    apply (post_facts_hold' rho3); [apply Forall_app in HF3 as [_ HS]; exact HS | exact H140]. }
  eapply etriple_conseq with (P := SPA segs Jc T3S rho3 tp);
    [intros w [Hsm HJ]; split; [apply smatchA_add_facts; [exact Hsm | exact HFS | rewrite HnT3; exact fb_factsS] | exact HJ] | intros w Hw; exact Hw |].
  apply (etriple_pre _ (FsHold rho3 FSS /\ FsBelow (ss_next (ax_S T3S)) FSS = true)); [intros w Hw; exact (fs_ok_sound Jc FSS T3S rho3 tp w fsS Hw) | intros [HFh HFb]].
  eapply (runp_etr Jc HJst FSS T3S E6s rho3 tp); [exact run3s | exact HlS | exact HFh | exact HFb |].
  intros rho6 Hag6.
  assert (Hn3S : ss_next (ax_S T3S) = 141%positive) by (unfold T3S, ax_add_facts, add_facts; destruct T3 as [S3 X3 b3]; cbn; cbn in HnT3; exact HnT3).
  rewrite Hn3S in Hag6. apply Pos.leb_le in HgeE6s.
  eapply etriple_conseq with (P := SPA segs Jc E6sS rho6 tp); [intros w Hw; exact (SPA_axforms segs _ _ rho6 E6s E6sS tp w xf6s Hw) | intros w Hw; exact Hw |].
  pose proof (agree_below_trans NF _ _ _ Hag3 (agree_below_le 141 NF _ _ ltac:(unfold NF; lia) Hag6)) as Hag06.
  pose proof (FirstNul_agree NF rho rho6 ltac:(reflexivity) Hag06 HFN) as HFN6.
  apply (call_completeA segs Jc Jn Jn Jc E6sS Pre_si s_sis R_sis Posts_si _ rho6 tp efr_sis chk_sis).
  - intros rhoc tpc. apply (etriple_pre _ (FirstNul rhoc)); [intros w [_ [_ H]]; exact H | intros HFNc].
    exact (si_sum_ex Jn Jn_stable rhoc tpc HFNc).
  - intros tr ms md Hsm HJ. split; [eapply HJinv; exact HJ | apply (FirstNul_callsub s_sis); [exact S16s | exact HFN6]].
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [HJ' _]. eapply HJinv; exact HJ'.
  - intros L rho7 tpL [<-|[]] Hag7. cbn [la_state]. rewrite imp_sis. rewrite <- HnE6s in Hag7.
    apply (etriple_pre _ (tpL = tp)); [intros w [Hsm HJ]; exact (HJtp _ _ _ _ HJ) | intros ->].
    pose proof (agree_below_trans NF _ _ _ Hag06 (agree_below_le (ss_next (ax_S E6s)) NF _ _ ltac:(unfold NF; lia) Hag7)) as Hag07.
    apply Hk; [exact Hag07| |].
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree NF rho3 rho7 p (agree_below_trans NF _ _ _ (agree_below_le 141 NF _ _ ltac:(unfold NF; lia) Hag6) (agree_below_le (ss_next (ax_S E6s)) NF _ _ ltac:(unfold NF; lia) Hag7))
               (proj1 (forallb_forall _ _) fb_facts p Hp))).
      exact (proj1 (Forall_forall _ _) HF3 p Hp). }
    destruct Hag6 as (A6 & _ & _). destruct Hag7 as (A7 & _ & _).
    rewrite <- (A7 140%positive) by lia. rewrite <- (A7 16%positive) by lia. rewrite <- (A6 140%positive) by lia. rewrite <- (A6 16%positive) by lia. exact H140.
Qed.

Lemma prefix_B_ex : ltac2:(tb__ "0|2|
S44OF_;S4fVrho;A1S1bZ41S1cS25Q40M0S4Vrho;P10M1A2A2Z1A2A2S2S6S30Vrho;R1A3S35S1S3R2A1S37A3S13S24G0A1S4R3P8cA2S4R3G1A2A3S42S0S16S0VJc;S32R4Vtp;A5R7A3F_;F_;F_;Frho7;S42S0S16S0VJc;S31Vrho;Vtp;A5R4A3F_;F_;F_;FQ;").
Proof.
  intros Q _ HzB Hk.
  destruct shapes as (HlP & HnP & HnE1 & HlE1 & _ & HnE2 & S16 & S12 & HnT3 & Hf140 & HlS & HlB & HnE6s & HgeE6s & S16s
                      & HnE4 & HgeE4 & HnT5 & HlT5F & HnE6b & HgeE6b & S16b & _).
  apply prefix_T3_ex; [exact HFN|]. intros rho3 Hag3 H140 HF3.
  assert (Hz3 : rw rho3 16 = rw rho 16) by (destruct Hag3 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HF3)) as HS3.
  assert (HFB : Forall (holds rho3) (factsB ++ facts_fps)).
  { apply Forall_app. split; [|exact HF3]. unfold factsB. constructor; [apply (GEU65_B' rho3 HS3 H140); rewrite Hz3; lia|].
    apply Forall_app. split; [exact (post_facts_hold' rho3 HS3 H140) | apply (big_facts_hold' rho3 HS3 H140); rewrite Hz3; lia]. }
  eapply etriple_conseq with (P := SPA segs Jc T3B rho3 tp);
    [intros w [Hsm HJ]; split; [apply smatchA_add_facts; [exact Hsm | exact HFB | rewrite HnT3; exact fb_factsB] | exact HJ] | intros w Hw; exact Hw |].
  eapply (erunA_tr segs 3000 CUTS_FPS T3B _ Jc rho3 tp); [exact run3b | exact HlB | apply HJst |].
  intros L rho4 [<-|[]] Hag4. cbn [la_state].
  assert (Hn3B : ss_next (ax_S T3B) = 141%positive) by (unfold T3B, ax_add_facts, add_facts; destruct T3 as [S3 X3 b3]; cbn; cbn in HnT3; exact HnT3).
  rewrite Hn3B in Hag4. apply Pos.leb_le in HgeE4. apply Pos.leb_le in HgeE6b.

  assert (Hsp4 : forall w, SPA segs Jc E4 rho4 tp w -> SPA segs Jc E4S rho4 tp w).
  { intros w Hw. pose proof split4 as Hs. unfold obindW in Hs.
    destruct (split_obj_at (ax_S E4) 1 (SLit (-2352))) as [S1|] eqn:E1s; [|discriminate].
    pose proof (SPA_split segs Jc rho4 E4 1 (SLit (-2352)) S1 tp w E1s Hw) as H1.
    pose proof (SPA_split segs Jc rho4 (ax_setS E4 S1) 1 (SLit (-2432)) (ax_S E4S) tp w Hs H1) as H2.
    rewrite ax_setS_setS, xs4 in H2. exact H2. }
  eapply etriple_conseq with (P := SPA segs Jc E4S rho4 tp); [exact Hsp4 | intros w Hw; exact Hw |].
  apply (call_completeA segs Jc Jc Jc Jc E4S Pre_rip s_rip R_rip Posts_rip _ rho4 tp efr_rip chk_rip).
  - intros rhoc tpc. exact (region_sum_ex Jc rhoc tpc (HJst NF)).
  - intros tr ms md Hsm HJ. eapply HJinv; exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. eapply HJinv; exact HJ'.
  - intros L rho5 tpL [<-|[]] Hag5. cbn [la_state]. rewrite imp_rip. rewrite <- HnE4 in Hag5.
    apply (etriple_pre _ (tpL = tp)); [intros w [Hsm HJ]; exact (HJtp _ _ _ _ HJ) | intros ->].
    pose proof (agree_below_trans 141 _ _ _ Hag4 (agree_below_le (ss_next (ax_S E4)) 141 _ _ HgeE4 Hag5)) as Hag35.
    assert (HFB5 : Forall (holds rho5) (SPEq (SVar 140) (SVar 16) :: factsB ++ facts_fps)).
    { apply (Forall_holds_agree 141 rho3 rho5); [exact Hag35 | exact fb_factsB' |]. constructor; [| exact HFB]. cbn [holds eval]. exact H140. }
    eapply etriple_conseq with (P := SPA segs Jc T5F rho5 tp);
      [intros w [Hsm HJ]; split; [apply smatchA_add_facts; [exact Hsm | exact HFB5 | rewrite HnT5; apply (forallb_sprop_below_le 181); [exact fb_factsB' | lia]] | exact HJ] | intros w Hw; exact Hw |].
    apply (etriple_pre _ (FsHold rho5 FSB /\ FsBelow (ss_next (ax_S T5F)) FSB = true)); [intros w Hw; exact (fs_ok_sound Jc FSB T5F rho5 tp w fsB Hw) | intros [HFh HFb]].
    eapply (runp_etr Jc HJst FSB T5F E6b rho5 tp); [exact run5 | exact HlT5F | exact HFh | exact HFb |].
    intros rho6 Hag6.
    assert (Hn5F : ss_next (ax_S T5F) = ss_next (ax_S T5)) by (unfold T5F, ax_add_facts, add_facts; destruct T5 as [S5 X5 b5]; reflexivity).
    rewrite Hn5F, HnT5 in Hag6.
    eapply etriple_conseq with (P := SPA segs Jc E6bS rho6 tp); [intros w Hw; exact (SPA_axforms segs _ _ rho6 E6b E6bS tp w xf6b Hw) | intros w Hw; exact Hw |].
    pose proof (agree_below_trans NF _ _ _ Hag3 (agree_below_le 141 NF _ _ ltac:(unfold NF; lia) (agree_below_trans 141 _ _ _ Hag35 (agree_below_le (ss_next (ax_S E4) + 40)%positive 141 _ _ ltac:(lia) Hag6)))) as Hag06.
    pose proof (FirstNul_agree NF rho rho6 ltac:(reflexivity) Hag06 HFN) as HFN6.
    apply (call_completeA segs Jc Jn Jn Jc E6bS Pre_si s_sib R_sib Posts_si _ rho6 tp efr_sib chk_sib).
    + intros rhoc tpc. apply (etriple_pre _ (FirstNul rhoc)); [intros w [_ [_ H]]; exact H | intros HFNc].
      exact (si_sum_ex Jn Jn_stable rhoc tpc HFNc).
    + intros tr ms md Hsm HJ. split; [eapply HJinv; exact HJ | apply (FirstNul_callsub s_sib); [exact S16b | exact HFN6]].
    + intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [HJ' _]. eapply HJinv; exact HJ'.
    + intros L rho7 tpL [<-|[]] Hag7. cbn [la_state]. rewrite imp_sib. rewrite <- HnE6b in Hag7.
      apply (etriple_pre _ (tpL = tp)); [intros w [Hsm HJ]; exact (HJtp _ _ _ _ HJ) | intros ->].
      assert (Hag67 : agree_below NF rho6 rho7) by (eapply (agree_below_le (ss_next (ax_S E6b)) NF); [unfold NF; lia | exact Hag7]).
      apply Hk; [eapply agree_below_trans; [exact Hag06 | exact Hag67] | |].
      { apply Forall_forall. intros p Hp.
        apply (proj1 (holds_agree NF rho3 rho7 p
                 (agree_below_trans NF _ _ _ (agree_below_le 141 NF _ _ ltac:(unfold NF; lia) (agree_below_trans 141 _ _ _ Hag35 (agree_below_le (ss_next (ax_S E4) + 40)%positive 141 _ _ ltac:(lia) Hag6))) Hag67)
                 (proj1 (forallb_forall _ _) fb_facts p Hp))).
        exact (proj1 (Forall_forall _ _) HF3 p Hp). }
      destruct Hag35 as (A35 & _ & _). destruct Hag6 as (A6 & _ & _). destruct Hag7 as (A7 & _ & _).
      rewrite <- (A7 140%positive) by lia. rewrite <- (A7 16%positive) by lia. rewrite <- (A6 140%positive) by lia. rewrite <- (A6 16%positive) by lia.
      rewrite <- (A35 140%positive) by lia. rewrite <- (A35 16%positive) by lia. exact H140.
Qed.

Theorem fpsA_sound_S_ex : ltac2:(tb__ "0|1|
S26S26S1A1A1S1bS1cVn;Z1A2Z40A2S1bS1cS1cVa;Vn;A2Vb;A2M0Z50A2S13S27S3cR3Vpre;Vsuf;Vn;G0S3aVa;Vn;VrA;S4dS33A5A6S28A3S42S0S16S0VJ0;S31Vrho;Vtp;A5S17S0VKwr;S29S24Q8A1S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A3F_;F_;F_;FLFs;").
Proof.
  intros LFs HzS Hfit Hok.
  apply (etriple_pre _ (length str = Z.to_nat n)); [intros w Hw; exact (str_len_of_SPA _ w Hw) | intros Hstr_len].
  destruct shapes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnE6s & HgeE6s & _ & _ & _ & _ & _ & _ & _ & _ & Hzv7 & Hn7 & _ & _ & Hz7 & _).
  destruct lenT7 as [Hl7 _]. apply Pos.leb_le in HgeE6s.
  unfold tailA_ok in Hok. destruct (tailA LFs pre suf n (a + n + b) (T8 a n rA factsS T7s)) as [o|] eqn:Hcert; [|discriminate]. clear Hok.
  pose proof (urange (rw rho 16)) as R16.
  apply (etriple_SPA_conseq_J segs _ (Kf 0)); [intros t md HJ; exact (J0_Kf0 t md HJ)|].
  apply (prefix_S_ex _ HFN HzS).
  intros rho7 Hag7 HFf H140.
  apply (etriple_pre _ (Forall (holds rho7) (ss_facts (ax_S T7s)))); [intros w [Hsm _]; exact (smatchA_facts segs rho7 tp T7s w Hsm) | intros HF7].
  assert (E16 : rw rho7 16 = rw rho 16) by (destruct Hag7 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HFf)) as HS7.
  assert (Hcls : Forall (holds rho7) factsS).
  { unfold factsS. constructor; [apply (GEU65_S' rho7 H140); rewrite E16; unfold n in HzS; lia | exact (post_facts_hold' rho7 HS7 H140)]. }
  pose proof (small_facts_hold rho7 T7s factsS Hag7 HF7 Hz7 HFf Hcls ltac:(unfold n, a, b in *; lia)) as HSF.
  destruct (T8_shape factsS T7s) as (HlT8 & HnT8 & HT8).
  eapply etriple_conseq with (P := SPA segs (Kf 0) (T8 a n rA factsS T7s) rho7 tp);
    [intros w Hw; apply (HT8 rho7 tp w HSF); [apply small_facts_below; [rewrite Hn7; lia | rewrite Hzv7, Hn7; lia | rewrite Hn7; apply (forallb_sprop_below_le 141); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | lia]] | exact Hw] | intros w Hw; exact Hw |].
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.tailA_sound_ex J0 pre suf str Hst0 Hfd2 rho tp ltac:(rewrite Hstr_len; reflexivity)
           n (a + n + b) ltac:(rewrite Hstr_len; unfold n; lia) ltac:(unfold a, b; lia) Hfit Hpre1 LFs (T8 a n rA factsS T7s) o Hcert
           ltac:(rewrite HlT8; exact Hl7) ltac:(rewrite HnT8, Hn7; unfold NF; lia) rho7 Hag7).
Qed.
Theorem fpsA_sound_B : ltac2:(tb__ "0|1|
S26S26S1A1A1S1bZ41S1cVn;Z1A2A2S1bS1cS1cVa;Vn;A2Vb;A2M0Z50A2S13S27S3cR3Vpre;Vsuf;Vn;G0S3aVa;Vn;VrA;S4cS32A5A6S28A3S43S0Vok;S16S0VJ0;S31Vrho;Vtp;A5S17S0VKwr;S29S24Q8A1S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A4F_;F_;F_;FLFs;").
Proof.
  intros LFs HzB Hfit Hok.
  apply (triple_pre ok _ (length str = Z.to_nat n)); [intros w Hw; exact (str_len_of_SPA _ w Hw) | intros Hstr_len].
  destruct shapes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnE4 & HgeE4 & HnT5 & _ & HnE6b & HgeE6b & _ & _ & _ & Hzv7 & Hn7 & _ & Hz7).
  destruct lenT7 as [_ Hl7]. apply Pos.leb_le in HgeE4. apply Pos.leb_le in HgeE6b. rewrite HnT5 in HgeE6b.
  unfold tailA_ok in Hok. destruct (tailA LFs pre suf n (a + n + b) (T8 a n rA factsB T7b)) as [o|] eqn:Hcert; [|discriminate]. clear Hok.
  pose proof (urange (rw rho 16)) as R16.
  apply (triple_SPA_conseq_J segs ok _ (Kf 0)); [intros t md HJ; exact (J0_Kf0 t md HJ)|].
  apply (prefix_B _ HFN HzB).
  intros rho7 Hag7 HFf H140.
  apply (triple_pre ok _ (Forall (holds rho7) (ss_facts (ax_S T7b)))); [intros w [Hsm _]; exact (smatchA_facts segs rho7 tp T7b w Hsm) | intros HF7].
  assert (E16 : rw rho7 16 = rw rho 16) by (destruct Hag7 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HFf)) as HS7.
  assert (Hcls : Forall (holds rho7) factsB).
  { unfold factsB. constructor; [apply (GEU65_B' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia |].
    apply Forall_app. split; [exact (post_facts_hold' rho7 HS7 H140) | apply (big_facts_hold' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia]. }
  pose proof (small_facts_hold rho7 T7b factsB Hag7 HF7 Hz7 HFf Hcls ltac:(unfold n, a, b in *; lia)) as HSF.
  destruct (T8_shape factsB T7b) as (HlT8 & HnT8 & HT8).
  eapply triple_conseq with (P := SPA segs (Kf 0) (T8 a n rA factsB T7b) rho7 tp);
    [intros w Hw; apply (HT8 rho7 tp w HSF); [apply small_facts_below; [rewrite Hn7; lia | rewrite Hzv7, Hn7; lia | rewrite Hn7; apply (forallb_sprop_below_le 141); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | lia]] | exact Hw] | intros w Hw; exact Hw |].
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.tailA_sound ok J0 pre suf str Hst0 Hfd2 HokK HokP rho tp ltac:(rewrite Hstr_len; reflexivity)
           n (a + n + b) ltac:(rewrite Hstr_len; unfold n; lia) ltac:(unfold a, b; lia) Hfit Hpre1 LFs (T8 a n rA factsB T7b) o Hcert
           ltac:(rewrite HlT8; exact Hl7) ltac:(rewrite HnT8, Hn7; unfold NF; lia) rho7 Hag7).
Qed.

Theorem fpsA_sound_B_ex : ltac2:(tb__ "0|1|
S26S26S1A1A1S1bZ41S1cVn;Z1A2A2S1bS1cS1cVa;Vn;A2Vb;A2M0Z50A2S13S27S3cR3Vpre;Vsuf;Vn;G0S3aVa;Vn;VrA;S4cS32A5A6S28A3S42S0S16S0VJ0;S31Vrho;Vtp;A5S17S0VKwr;S29S24Q8A1S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A3F_;F_;F_;FLFs;").
Proof.
  intros LFs HzB Hfit Hok.
  apply (etriple_pre _ (length str = Z.to_nat n)); [intros w Hw; exact (str_len_of_SPA _ w Hw) | intros Hstr_len].
  destruct shapes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnE4 & HgeE4 & HnT5 & _ & HnE6b & HgeE6b & _ & _ & _ & Hzv7 & Hn7 & _ & Hz7).
  destruct lenT7 as [_ Hl7]. apply Pos.leb_le in HgeE4. apply Pos.leb_le in HgeE6b. rewrite HnT5 in HgeE6b.
  unfold tailA_ok in Hok. destruct (tailA LFs pre suf n (a + n + b) (T8 a n rA factsB T7b)) as [o|] eqn:Hcert; [|discriminate]. clear Hok.
  pose proof (urange (rw rho 16)) as R16.
  apply (etriple_SPA_conseq_J segs _ (Kf 0)); [intros t md HJ; exact (J0_Kf0 t md HJ)|].
  apply (prefix_B_ex _ HFN HzB).
  intros rho7 Hag7 HFf H140.
  apply (etriple_pre _ (Forall (holds rho7) (ss_facts (ax_S T7b)))); [intros w [Hsm _]; exact (smatchA_facts segs rho7 tp T7b w Hsm) | intros HF7].
  assert (E16 : rw rho7 16 = rw rho 16) by (destruct Hag7 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HFf)) as HS7.
  assert (Hcls : Forall (holds rho7) factsB).
  { unfold factsB. constructor; [apply (GEU65_B' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia |].
    apply Forall_app. split; [exact (post_facts_hold' rho7 HS7 H140) | apply (big_facts_hold' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia]. }
  pose proof (small_facts_hold rho7 T7b factsB Hag7 HF7 Hz7 HFf Hcls ltac:(unfold n, a, b in *; lia)) as HSF.
  destruct (T8_shape factsB T7b) as (HlT8 & HnT8 & HT8).
  eapply etriple_conseq with (P := SPA segs (Kf 0) (T8 a n rA factsB T7b) rho7 tp);
    [intros w Hw; apply (HT8 rho7 tp w HSF); [apply small_facts_below; [rewrite Hn7; lia | rewrite Hzv7, Hn7; lia | rewrite Hn7; apply (forallb_sprop_below_le 141); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | lia]] | exact Hw] | intros w Hw; exact Hw |].
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.tailA_sound_ex J0 pre suf str Hst0 Hfd2 rho tp ltac:(rewrite Hstr_len; reflexivity)
           n (a + n + b) ltac:(rewrite Hstr_len; unfold n; lia) ltac:(unfold a, b; lia) Hfit Hpre1 LFs (T8 a n rA factsB T7b) o Hcert
           ltac:(rewrite HlT8; exact Hl7) ltac:(rewrite HnT8, Hn7; unfold NF; lia) rho7 Hag7).
Qed.

Lemma rl3_len_of_SPA : ltac2:(tb__ "0|0|
S18S44S16S0R2S31Vrho;Vtp;R1A6S13S4bS23S29S24Q8A1SdVrho;P3A2A2A1S25Q40S4Vrho;P11A2A2A3F_;Fw;FJ;").
Proof.
  intros J w [(Hsm & _) _].
  pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  pose proof (proj1 (Forall_forall _ _) Hall _ (nth_error_In _ _ Pre_str)) as Ho.
  destruct Ho as (_ & _ & _ & _ & Hinv). cbn [ob_dflt O_strS dflt_inv ob_lo ob_hi] in Hinv.
  unfold obj_lo_of, obj_hi_of, O_strS in Hinv. cbn [ob_lo ob_hi] in Hinv. rewrite soff_lit_small in Hinv by lia.
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF. rewrite Pre_facts in HF. pose proof (proj2 (proj1 (Forall_app _ _ _) HF)) as HS.
  destruct (str_factsZ rho HS) as (Z1 & Z2 & _). pose proof (urange (rw rho 17)) as R17.
  assert (Hhi : soff rho (SVar 17) = bv_unsigned (rw rho 17)) by (unfold soff; cbn [eval]; apply signed_small; lia).
  rewrite Hhi in Hinv. lia.
Qed.
Lemma nmax_of_SPA : ltac2:(tb__ "0|0|
S18S44S16S0R2S31Vrho;Vtp;R1A6S1bVn;Z1ffffA2F_;Fw;FJ;").
Proof.
  intros J w [(Hsm & _) _]. pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF. rewrite Pre_facts in HF. pose proof (proj2 (proj1 (Forall_app _ _ _) HF)) as HS.
  unfold str_facts in HS. do 15 (apply Forall_inv_tail in HS). pose proof (Forall_inv HS) as X. cbn [holds eval] in X.
  rewrite lit_unsigned in X. change (131071 mod 2 ^ 64) with 131071 in X. unfold n. exact X.
Qed.
Lemma T8C_shape : ltac2:(tb__ "0|3|
S47S14S13S27SaS46S58Va;R1A2A1M0A1SaS46R1A1M1A1A3S14S13S4aS7G0A1S7G1A1A3S2S26S24Q40A1A1S44S35S1S3R3A1S59Va;S38R4A1A2A3S13S27S48S1S5S7S46R5A1A1A1S59Va;S38R5A1A2A3S28A3S16S0VKf;U0A1M2R6R5R4R3A6S16S0G2S58Va;R7A2R6R5R4A6F_;F_;F_;Fw;Ftpx;Frho7;A2A2FT7;").
Proof.
  intros T7. unfold T8C, ax_add_facts, add_facts. destruct T7 as [S7 X7 b7]. cbn. split; [reflexivity|]. split; [reflexivity|].
  intros rho7 tpx w HF Hb Hsp. exact (SPA_add_facts _ rho7 tpx _ {| ax_S := S7; ax_X := X7; ax_base := b7 |} w HF Hb Hsp).
Qed.
Lemma big_facts_C_hold : ltac2:(tb__ "0|1|
S2S6S30Vrho;R1A3S35S1S3R2A1ScS46S32A1A1A3S35S1S3R3A1S37A3S35S1S3R4A1S4cA3S1fS1dZ50M0Va;A2Vn;A2S1bVa;G0A2S35S1S3R7A1S59Va;S38S32A1A2A3F_;F_;F_;F_;F_;F_;Frho7;").
Proof.
  intros rho7 Hag HF7 HFf Hcls Hbig Ha80.
  destruct shapes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hz).
  apply existsb_exists in Hz as (q & Hq & Eq). apply sprop_eqb_sound in Eq. subst q.
  pose proof (proj1 (Forall_forall _ _) HF7 _ Hq) as Ez. cbn [holds eval] in Ez.
  pose proof Hag as (A & L & _). assert (E16 : rw rho7 16 = rw rho 16) by (symmetry; apply A; reflexivity).
  assert (HFN7 : FirstNul rho7) by (eapply (FirstNul_agree NF); [reflexivity | exact Hag | exact HFN]).
  pose proof (urange (rw rho 16)) as R16.
  unfold big_facts_C. apply Forall_app. split; [| apply Forall_app; split; [exact Hcls | exact HFf]].
  constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (proj2 (holds_BZ rho7 (SVar (zvar T7b)))). cbn [eval]. rewrite Ez. exact (proj1 HFN7).
  - unfold FWBIG, FWSMALL. cbn [holds branch_taken eval]. unfold bv_ltu. rewrite Ez, E16, lit_unsigned, Z.mod_small by (unfold a in *; lia).
    destruct (Z.ltb_spec (80 - a) (bv_unsigned (rw rho 16))); [cbn; congruence | exfalso; unfold n, a in *; lia].
  -
    pose proof (LOWV_of_facts rho7 HFf) as (_ & _ & _ & _ & _ & L6).
    destruct (str_factsZ rho7 (proj2 (proj1 (Forall_app _ _ _) HFf))) as (Z1 & _ & Z3 & _ & Z5 & Z6 & _).
    unfold URNG. cbn [holds]. cbn [eval]. rewrite add_val. change (eval rho7 sX) with (eval rho7 sX) in *.
    cbn [eval] in L6. rewrite L6, Ez, E16, lit_unsigned. change ((2 ^ 47 - 16) mod 2 ^ 64) with (2 ^ 47 - 16).
    rewrite <- E16 in *. pose proof (urange (rw rho7 18)). pose proof (urange (rw rho7 20)). rewrite Z.mod_small; lia.
Qed.
Lemma big_facts_C_below : ltac2:(tb__ "0|0|
S4aS4aS56P8dR2A2S57R2R3A2S13S27S48S1S5R4A1S59Va;R3A2A3S28A3F_;F_;Fzv;Fnx;").
Proof.
  intros nx zv Hnx Hzv. unfold big_facts_C. rewrite forallb_app. rewrite (forallb_sprop_below_le 141 nx _ fb_factsB Hnx).
  assert (Zv : (zv <? nx)%positive = true) by (apply Pos.ltb_lt; lia).
  assert (Z18 : (18 <? nx)%positive = true) by (apply Pos.ltb_lt; lia).
  assert (Z20 : (20 <? nx)%positive = true) by (apply Pos.ltb_lt; lia).
  cbn -[Pos.ltb]. rewrite ?Zv, ?Z18, ?Z20. reflexivity.
Qed.

Theorem fpsC_sound_C : ltac2:(tb__ "0|1|
S1bZ41S1cVn;Z1A2A2S1fS1dZ50M0Va;A2Vn;A2S1bVa;G0A2S13S27S5aVpre;Vsuf;Va;S38S32A1S58Va;S32A2A5S28A3S43S0Vok;S16S0VJ0;S31Vrho;Vtp;A5S17S0VKwr;S29S24Q8A1S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A4F_;F_;F_;F_;").
Proof.
  intros HzB Hbig Ha80 Hok.
  apply (triple_pre ok _ (length str = Z.to_nat n)); [intros w Hw; exact (str_len_of_SPA _ w Hw) | intros Hstr_len].
  apply (triple_pre ok _ (Z.of_nat (length (rl rho 3)) = bv_unsigned (rw rho 17))); [intros w Hw; exact (rl3_len_of_SPA _ w Hw) | intros HA3].
  apply (triple_pre ok _ (n <= 131071)); [intros w Hw; exact (nmax_of_SPA _ w Hw) | intros Hnmax].
  destruct shapes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnE4 & HgeE4 & HnT5 & _ & HnE6b & HgeE6b & _ & _ & _ & Hzv7 & Hn7 & _ & Hz7).
  destruct lenT7 as [_ Hl7]. apply Pos.leb_le in HgeE4. apply Pos.leb_le in HgeE6b. rewrite HnT5 in HgeE6b.
  unfold tailC_ok in Hok. destruct (tailC pre suf a (zvar T7b) (T8C a T7b)) as [o|] eqn:Hcert; [|discriminate]. clear Hok.
  pose proof (urange (rw rho 16)) as R16.
  apply (triple_SPA_conseq_J segs ok _ (Kf 0)); [intros t md HJ; exact (J0_Kf0 t md HJ)|].
  apply (prefix_B _ HFN HzB).
  intros rho7 Hag7 HFf H140.
  apply (triple_pre ok _ (Forall (holds rho7) (ss_facts (ax_S T7b)))); [intros w [Hsm _]; exact (smatchA_facts segs rho7 tp T7b w Hsm) | intros HF7].
  assert (E16 : rw rho7 16 = rw rho 16) by (destruct Hag7 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HFf)) as HS7.
  assert (Hcls : Forall (holds rho7) factsB).
  { unfold factsB. constructor; [apply (GEU65_B' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia |].
    apply Forall_app. split; [exact (post_facts_hold' rho7 HS7 H140) | apply (big_facts_hold' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia]. }
  pose proof (big_facts_C_hold rho7 Hag7 HF7 HFf Hcls Hbig Ha80) as HBF.
  destruct (T8C_shape T7b) as (HlT8 & HnT8 & HT8).
  eapply triple_conseq with (P := SPA segs (Kf 0) (T8C a T7b) rho7 tp);
    [intros w Hw; apply (HT8 rho7 tp w HBF); [apply big_facts_C_below; [rewrite Hn7; lia | rewrite Hzv7, Hn7; lia] | exact Hw] | intros w Hw; exact Hw |].
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Fps_tailC.tailC_sound ok J0 pre suf str Hst0 Hfd2 HokK HokP rho tp ltac:(rewrite Hstr_len; reflexivity)
           ltac:(rewrite Hstr_len; unfold n; lia) HA3 a (zvar T7b) (T8C a T7b) o Hcert
           ltac:(rewrite HlT8; exact Hl7) ltac:(rewrite HnT8, Hn7; unfold NF; lia) ltac:(rewrite Hstr_len; unfold n in *; lia) rho7 Hag7).
Qed.

Theorem fpsC_sound_C_ex : ltac2:(tb__ "0|1|
S1bZ41S1cVn;Z1A2A2S1fS1dZ50M0Va;A2Vn;A2S1bVa;G0A2S13S27S5aVpre;Vsuf;Va;S38S32A1S58Va;S32A2A5S28A3S42S0S16S0VJ0;S31Vrho;Vtp;A5S17S0VKwr;S29S24Q8A1S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A3F_;F_;F_;F_;").
Proof.
  intros HzB Hbig Ha80 Hok.
  apply (etriple_pre _ (length str = Z.to_nat n)); [intros w Hw; exact (str_len_of_SPA _ w Hw) | intros Hstr_len].
  apply (etriple_pre _ (Z.of_nat (length (rl rho 3)) = bv_unsigned (rw rho 17))); [intros w Hw; exact (rl3_len_of_SPA _ w Hw) | intros HA3].
  apply (etriple_pre _ (n <= 131071)); [intros w Hw; exact (nmax_of_SPA _ w Hw) | intros Hnmax].
  destruct shapes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnE4 & HgeE4 & HnT5 & _ & HnE6b & HgeE6b & _ & _ & _ & Hzv7 & Hn7 & _ & Hz7).
  destruct lenT7 as [_ Hl7]. apply Pos.leb_le in HgeE4. apply Pos.leb_le in HgeE6b. rewrite HnT5 in HgeE6b.
  unfold tailC_ok in Hok. destruct (tailC pre suf a (zvar T7b) (T8C a T7b)) as [o|] eqn:Hcert; [|discriminate]. clear Hok.
  pose proof (urange (rw rho 16)) as R16.
  apply (etriple_SPA_conseq_J segs _ (Kf 0)); [intros t md HJ; exact (J0_Kf0 t md HJ)|].
  apply (prefix_B_ex _ HFN HzB).
  intros rho7 Hag7 HFf H140.
  apply (etriple_pre _ (Forall (holds rho7) (ss_facts (ax_S T7b)))); [intros w [Hsm _]; exact (smatchA_facts segs rho7 tp T7b w Hsm) | intros HF7].
  assert (E16 : rw rho7 16 = rw rho 16) by (destruct Hag7 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HFf)) as HS7.
  assert (Hcls : Forall (holds rho7) factsB).
  { unfold factsB. constructor; [apply (GEU65_B' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia |].
    apply Forall_app. split; [exact (post_facts_hold' rho7 HS7 H140) | apply (big_facts_hold' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia]. }
  pose proof (big_facts_C_hold rho7 Hag7 HF7 HFf Hcls Hbig Ha80) as HBF.
  destruct (T8C_shape T7b) as (HlT8 & HnT8 & HT8).
  eapply etriple_conseq with (P := SPA segs (Kf 0) (T8C a T7b) rho7 tp);
    [intros w Hw; apply (HT8 rho7 tp w HBF); [apply big_facts_C_below; [rewrite Hn7; lia | rewrite Hzv7, Hn7; lia] | exact Hw] | intros w Hw; exact Hw |].
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Fps_tailC.tailC_sound_ex J0 pre suf str Hst0 Hfd2 rho tp ltac:(rewrite Hstr_len; reflexivity)
           ltac:(rewrite Hstr_len; unfold n; lia) HA3 a (zvar T7b) (T8C a T7b) o Hcert
           ltac:(rewrite HlT8; exact Hl7) ltac:(rewrite HnT8, Hn7; unfold NF; lia) ltac:(rewrite Hstr_len; unfold n in *; lia) rho7 Hag7).
Qed.

Definition tail_stmt (T8x : axst) : Prop := ltac2:(tb__ "0|2|
S13S2aS29S24Q8A1M0Vstr;A2S20Vn;A1A3S13S27SaS46VT8x;A1M1A1S2dA3S56S30S7G1A1A2S2S6S30Vrho;R1A3S43S0Vok;S16S0VKf;U0A1VT8x;R2Vtp;A5S17S0VKwr;S29G0S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A4F_;Frho7;F_;F_;F_;").
Definition tail_stmt_ex (T8x : axst) : Prop := ltac2:(tb__ "0|2|
S13S2aS29S24Q8A1M0Vstr;A2S20Vn;A1A3S13S27SaS46VT8x;A1M1A1S2dA3S56S30S7G1A1A2S2S6S30Vrho;R1A3S42S0S16S0VKf;U0A1VT8x;R2Vtp;A5S17S0VKwr;S29G0S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A3F_;Frho7;F_;F_;F_;").

Theorem fps_sound_S_gen : ltac2:(tb__ "0|0|
S1bS1cVn;Z1A2Z40A2S1bVn;S1dZ50Va;A2A2S5fS3aVa;Vn;VrA;S4dS33A5A1S43S0Vok;S16S0VJ0;S31Vrho;Vtp;A5S17S0VKwr;S29S24Q8A1S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A4F_;F_;F_;").
Proof.
  intros HzS Hna Htail.
  apply (triple_pre ok _ (length str = Z.to_nat n)); [intros w Hw; exact (str_len_of_SPA _ w Hw) | intros Hstr_len].
  destruct shapes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnE6s & HgeE6s & _ & _ & _ & _ & _ & _ & _ & _ & Hzv7 & Hn7 & _ & _ & Hz7 & _).
  destruct lenT7 as [Hl7 _]. apply Pos.leb_le in HgeE6s.
  pose proof (urange (rw rho 16)) as R16.
  apply (triple_SPA_conseq_J segs ok _ (Kf 0)); [intros t md HJ; exact (J0_Kf0 t md HJ)|].
  apply (prefix_S _ HFN HzS).
  intros rho7 Hag7 HFf H140.
  apply (triple_pre ok _ (Forall (holds rho7) (ss_facts (ax_S T7s)))); [intros w [Hsm _]; exact (smatchA_facts segs rho7 tp T7s w Hsm) | intros HF7].
  assert (E16 : rw rho7 16 = rw rho 16) by (destruct Hag7 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HFf)) as HS7.
  assert (Hcls : Forall (holds rho7) factsS).
  { unfold factsS. constructor; [apply (GEU65_S' rho7 H140); rewrite E16; unfold n in HzS; lia | exact (post_facts_hold' rho7 HS7 H140)]. }
  pose proof (small_facts_hold rho7 T7s factsS Hag7 HF7 Hz7 HFf Hcls Hna) as HSF.
  destruct (T8_shape factsS T7s) as (HlT8 & HnT8 & HT8).
  eapply triple_conseq with (P := SPA segs (Kf 0) (T8 a n rA factsS T7s) rho7 tp);
    [intros w Hw; apply (HT8 rho7 tp w HSF); [apply small_facts_below; [rewrite Hn7; lia | rewrite Hzv7, Hn7; lia | rewrite Hn7; apply (forallb_sprop_below_le 141); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | lia]] | exact Hw] | intros w Hw; exact Hw |].
  exact (Htail Hstr_len ltac:(rewrite HlT8; exact Hl7) ltac:(rewrite HnT8, Hn7; unfold NF; lia) rho7 Hag7).
Qed.

Theorem fps_sound_S_gen_ex : ltac2:(tb__ "0|0|
S1bS1cVn;Z1A2Z40A2S1bVn;S1dZ50Va;A2A2S60S3aVa;Vn;VrA;S4dS33A5A1S42S0S16S0VJ0;S31Vrho;Vtp;A5S17S0VKwr;S29S24Q8A1S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A3F_;F_;F_;").
Proof.
  intros HzS Hna Htail.
  apply (etriple_pre _ (length str = Z.to_nat n)); [intros w Hw; exact (str_len_of_SPA _ w Hw) | intros Hstr_len].
  destruct shapes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnE6s & HgeE6s & _ & _ & _ & _ & _ & _ & _ & _ & Hzv7 & Hn7 & _ & _ & Hz7 & _).
  destruct lenT7 as [Hl7 _]. apply Pos.leb_le in HgeE6s.
  pose proof (urange (rw rho 16)) as R16.
  apply (etriple_SPA_conseq_J segs _ (Kf 0)); [intros t md HJ; exact (J0_Kf0 t md HJ)|].
  apply (prefix_S_ex _ HFN HzS).
  intros rho7 Hag7 HFf H140.
  apply (etriple_pre _ (Forall (holds rho7) (ss_facts (ax_S T7s)))); [intros w [Hsm _]; exact (smatchA_facts segs rho7 tp T7s w Hsm) | intros HF7].
  assert (E16 : rw rho7 16 = rw rho 16) by (destruct Hag7 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HFf)) as HS7.
  assert (Hcls : Forall (holds rho7) factsS).
  { unfold factsS. constructor; [apply (GEU65_S' rho7 H140); rewrite E16; unfold n in HzS; lia | exact (post_facts_hold' rho7 HS7 H140)]. }
  pose proof (small_facts_hold rho7 T7s factsS Hag7 HF7 Hz7 HFf Hcls Hna) as HSF.
  destruct (T8_shape factsS T7s) as (HlT8 & HnT8 & HT8).
  eapply etriple_conseq with (P := SPA segs (Kf 0) (T8 a n rA factsS T7s) rho7 tp);
    [intros w Hw; apply (HT8 rho7 tp w HSF); [apply small_facts_below; [rewrite Hn7; lia | rewrite Hzv7, Hn7; lia | rewrite Hn7; apply (forallb_sprop_below_le 141); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | lia]] | exact Hw] | intros w Hw; exact Hw |].
  exact (Htail Hstr_len ltac:(rewrite HlT8; exact Hl7) ltac:(rewrite HnT8, Hn7; unfold NF; lia) rho7 Hag7).
Qed.

Theorem fps_sound_B_gen : ltac2:(tb__ "0|0|
S1bZ41S1cVn;Z1A2A2S1bVn;S1dZ50Va;A2A2S5fS3aVa;Vn;VrA;S4cS32A5A1S43S0Vok;S16S0VJ0;S31Vrho;Vtp;A5S17S0VKwr;S29S24Q8A1S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A4F_;F_;F_;").
Proof.
  intros HzB Hna Htail.
  apply (triple_pre ok _ (length str = Z.to_nat n)); [intros w Hw; exact (str_len_of_SPA _ w Hw) | intros Hstr_len].
  destruct shapes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnE4 & HgeE4 & HnT5 & _ & HnE6b & HgeE6b & _ & _ & _ & Hzv7 & Hn7 & _ & Hz7).
  destruct lenT7 as [_ Hl7]. apply Pos.leb_le in HgeE4. apply Pos.leb_le in HgeE6b. rewrite HnT5 in HgeE6b.
  pose proof (urange (rw rho 16)) as R16.
  apply (triple_SPA_conseq_J segs ok _ (Kf 0)); [intros t md HJ; exact (J0_Kf0 t md HJ)|].
  apply (prefix_B _ HFN HzB).
  intros rho7 Hag7 HFf H140.
  apply (triple_pre ok _ (Forall (holds rho7) (ss_facts (ax_S T7b)))); [intros w [Hsm _]; exact (smatchA_facts segs rho7 tp T7b w Hsm) | intros HF7].
  assert (E16 : rw rho7 16 = rw rho 16) by (destruct Hag7 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HFf)) as HS7.
  assert (Hcls : Forall (holds rho7) factsB).
  { unfold factsB. constructor; [apply (GEU65_B' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia |].
    apply Forall_app. split; [exact (post_facts_hold' rho7 HS7 H140) | apply (big_facts_hold' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia]. }
  pose proof (small_facts_hold rho7 T7b factsB Hag7 HF7 Hz7 HFf Hcls Hna) as HSF.
  destruct (T8_shape factsB T7b) as (HlT8 & HnT8 & HT8).
  eapply triple_conseq with (P := SPA segs (Kf 0) (T8 a n rA factsB T7b) rho7 tp);
    [intros w Hw; apply (HT8 rho7 tp w HSF); [apply small_facts_below; [rewrite Hn7; lia | rewrite Hzv7, Hn7; lia | rewrite Hn7; apply (forallb_sprop_below_le 141); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | lia]] | exact Hw] | intros w Hw; exact Hw |].
  exact (Htail Hstr_len ltac:(rewrite HlT8; exact Hl7) ltac:(rewrite HnT8, Hn7; unfold NF; lia) rho7 Hag7).
Qed.

Theorem fps_sound_B_gen_ex : ltac2:(tb__ "0|0|
S1bZ41S1cVn;Z1A2A2S1bVn;S1dZ50Va;A2A2S60S3aVa;Vn;VrA;S4cS32A5A1S42S0S16S0VJ0;S31Vrho;Vtp;A5S17S0VKwr;S29S24Q8A1S3fVpre;Vsuf;Vstr;A3A2A1S30Vrho;Vtp;S39A6A3F_;F_;F_;").
Proof.
  intros HzB Hna Htail.
  apply (etriple_pre _ (length str = Z.to_nat n)); [intros w Hw; exact (str_len_of_SPA _ w Hw) | intros Hstr_len].
  destruct shapes as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnE4 & HgeE4 & HnT5 & _ & HnE6b & HgeE6b & _ & _ & _ & Hzv7 & Hn7 & _ & Hz7).
  destruct lenT7 as [_ Hl7]. apply Pos.leb_le in HgeE4. apply Pos.leb_le in HgeE6b. rewrite HnT5 in HgeE6b.
  pose proof (urange (rw rho 16)) as R16.
  apply (etriple_SPA_conseq_J segs _ (Kf 0)); [intros t md HJ; exact (J0_Kf0 t md HJ)|].
  apply (prefix_B_ex _ HFN HzB).
  intros rho7 Hag7 HFf H140.
  apply (etriple_pre _ (Forall (holds rho7) (ss_facts (ax_S T7b)))); [intros w [Hsm _]; exact (smatchA_facts segs rho7 tp T7b w Hsm) | intros HF7].
  assert (E16 : rw rho7 16 = rw rho 16) by (destruct Hag7 as (A & _ & _); symmetry; apply A; reflexivity).
  pose proof (proj2 (proj1 (Forall_app _ _ _) HFf)) as HS7.
  assert (Hcls : Forall (holds rho7) factsB).
  { unfold factsB. constructor; [apply (GEU65_B' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia |].
    apply Forall_app. split; [exact (post_facts_hold' rho7 HS7 H140) | apply (big_facts_hold' rho7 HS7 H140); rewrite E16; unfold n in HzB; lia]. }
  pose proof (small_facts_hold rho7 T7b factsB Hag7 HF7 Hz7 HFf Hcls Hna) as HSF.
  destruct (T8_shape factsB T7b) as (HlT8 & HnT8 & HT8).
  eapply etriple_conseq with (P := SPA segs (Kf 0) (T8 a n rA factsB T7b) rho7 tp);
    [intros w Hw; apply (HT8 rho7 tp w HSF); [apply small_facts_below; [rewrite Hn7; lia | rewrite Hzv7, Hn7; lia | rewrite Hn7; apply (forallb_sprop_below_le 141); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | lia]] | exact Hw] | intros w Hw; exact Hw |].
  exact (Htail Hstr_len ltac:(rewrite HlT8; exact Hl7) ltac:(rewrite HnT8, Hn7; unfold NF; lia) rho7 Hag7).
Qed.
End Rho.
End SumA.
End FpsSum.
End Fps_prefix.

