(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_025.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.

(* [comment removed for export] *)
Module DrvR_tstates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "la_state"; "xr_eqb"; "mkLeafA"; "ax_setS"; "la_reason"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nat"; "option"; "Some"; "true"; "prod"; "bool"; "nil"; "pair"; "length"; "app"; "false"; "andb"; "negb"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "sv"; "ss_objs"; "sstate"; "sprop"; "sv_eqb"; "SAlu"; "ss_facts"; "ss_next"; "ss_pc"; "SPBranch"; "SPNot"; "mkSS"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "set_objs"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates"; "selA"; "x4set"; "splitA"; "x4_okb"; "pcs"; "app_objs"; "fw_rtc"; "fw_u2"; "fw_u1"; "fw_undo1"; "E_oom"; "E_ov1"; "E_ref"; "E_sh0"; "E_sh1"; "E_shZ"; "U_ov1"; "U_ref"; "U_sh0"; "U_sh1"; "U_shZ"; "fw_undo2L"; "mergeA"; "CF_ov1"; "CF_sh0"; "CF_sh1"; "CF_shZ"; "C_oom"; "C_ov1"; "C_ref"; "C_sh0"; "C_sh1"; "C_shZ"; "T_oom"; "T_ov1"; "T_ref"; "T_sh0"; "T_sh1"; "T_shZ"; "U_oom"; "V_ov1"; "V_sh0"; "V_sh1"; "V_shZ"; "addX"; "fb_siteR"; "fw_siteL"; "RF_ov1"; "RF_sh0"; "RF_sh1"; "RF_shZ"; "R_oom"; "R_ov1"; "R_ref"; "R_sh0"; "R_sh1"; "R_shZ"; "V_oom"; "V_ref"; "exS_idxs"; "ex_carvedR"; "ex_img"; "fp_rtc"; "sF_ov1"; "sF_sh0"; "sF_sh1"; "sF_shZ"; "s_oom"; "s_ov1"; "s_ref"; "s_sh0"; "s_sh1"; "s_shZ"; "LV_fov1"; "LV_fsh0"; "LV_fsh1"; "LV_fshZ"; "LV_xoom"; "LV_xov1"; "LV_xref"; "LV_xsh0"; "LV_xsh1"; "LV_xshZ"; "TF_ov1"; "TF_sh0"; "TF_sh1"; "TF_shZ"; "W_ov1"; "W_sh0"; "W_sh1"; "W_shZ"; "exS_rb"; "ex_fin"; "ex_img_okb"; "ex_okb"; "firstA"; "fp_hints"; "fp_u1"; "fp_u2"; "s_exR"; "CX_oom"; "CX_ov1"; "CX_ref"; "CX_sh0"; "CX_sh1"; "CX_shZ"; "F_ov1"; "F_sh0"; "F_sh1"; "F_shZ"; "X_oom"; "X_ov1"; "X_ref"; "X_sh0"; "X_sh1"; "X_shZ"; "ex_siteD"; "ex_siteS"; "fp_site"; "fp_undo1"; "fp_undo2"; "fw_siteM"; "fw_undo2M"; "ms16_at"; "s_fpc"; "x4d_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXRebase"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "Pre_fw"; "xblk"; "P_fw"; "Posts_fw"; "EBUF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states"; "CUTS_R"; "T_after"; "ax_of"; "optS"; "Loom"; "Lov1"; "Lref"; "Lsh0"; "Lsh1"; "LshZ"; "has_tpfact"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "PreF"; "vTP"; "PostF"; "locate"; "DEEP"; "sp0"; "vCap"; "dropX"; "spM"; "vB"; "s_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "free_stub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@Corelib.Lists.ListDef"; "map"; "seq"; "firstn"; "@Stdlib.Lists.List"; "existsb"; "In"; "flat_map"; "forallb"; "@Corelib.Init.Nat"; "sub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "exit_entry"; "FERR"; "Pre_exit0"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "add"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface"; "Pre_ref"; "P_ref"; "Posts_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_OR"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR"; "CAP0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "O_realm"; "O_rtc3w"; "ms16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sprop_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform DrvGlueA DrvGlueB SysStepA SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFpIface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition app_objs (l : list sobj) (A : axst) : axst := ltac2:(tb__ "0|1|
SaVA;S35S3VA;A1M0S17S1cS1fG0A1Vl;A3A2A2").

Definition addX (r : sv * sv) (A : axst) : axst := ltac2:(tb__ "0|2|
S13S2L_;SdfS12S1eS1eA2M0S8Vr;A1S6VA;A1M1A3VA;SefVA;ScG0Vr;G1A3A2X13x2").
Definition selA (idxs : list nat) (A : axst) : axst := ltac2:(tb__ "0|1|
SaVA;S35S3VA;A1M0Sf9S1fG0A1Vidxs;A2A2A2").
Definition firstA (n : nat) (A : axst) : axst := ltac2:(tb__ "0|1|
SaVA;S35S3VA;A1M0SdeS1cVn;S1fG0A1A3A2A2").
Definition mergeA (i : nat) (A : axst) : axst := ltac2:(tb__ "0|0|
Sc1VA;SdbS3VA;A1Vi;A2A2").
Definition splitA (i : nat) (mid : sv) (A : axst) : axst := ltac2:(tb__ "0|0|
Sc1VA;SdaS3VA;A1Vi;Vmid;A3A2").
Definition pcs (l : list leafA) : ltac2:(tb__ "0|0|
SdS12S31S33A2A1") := ltac2:(tb__ "0|0|
SdcS4S12S31S33A2S4S15S31S33S26S3S7R1A1A1A1SbR1A1A4LL;Vl;A4").

Definition x4set (e : sv) (A : axst) : axst := ltac2:(tb__ "0|0|
S3VA;A1S20SaVA;S29S26R1A1S36S1eS2eR1A1U4Ve;A4S2cR1A1S2bR1A1S2fR1A1S1fR1A1S24R1A1S25R1A1S2dR1A1A9A2TS;").
Definition x4d_okb (d : list (sv * sv)) : bool := ltac2:(tb__ "0|3|
SdS12S1eS1eA2M0A1M1S13Ld;Vd;S11G0G1G0S13Lp;R2S1eS1eG1S13Ll;R3S1bS19S22R2ScbA2S22R1S1dSd5A1M2A2A2S19S22R2G2A2S22R1ScbA2A2A2G0G1S18Ll0;Lp0;Xdx2Lb;La;X12x1Ll;Lp;Xdx2").
Definition x4_okb (A : axst) (e : sv) : bool := ltac2:(tb__ "0|4|
S19S19S30S3S38Ve;VA;A2A1M0A1SfS12SdS12S1eS1eA2A1M1SdS21A1M2A2M3A1S13Lx;Sf8S3VA;A1G0A2G3G3S13Lp;R1G1G2G2S13Ll;R1Sb4R2A1S21G2S18Ll0;Ls;Xdx2Ll;Ld;X12x1Lp;S18Xfx2A2Sc8VA;A1A2").

Definition fw_rtc : list sobj := [O_rtc3w].
Definition fw_siteL (msg len : Z) (E : axst) : axst := ltac2:(tb__ "0|0|
S63SbaVmsg;Vlen;A2S3cS3dS39U0S1dN9e0A1S38S1dSd5A1VE;A2A3A2A2").
Definition fw_siteM (msg len : Z) (E : axst) : axst := ltac2:(tb__ "0|0|
S63SbaVmsg;Vlen;A2S3cS3dS39U0S1dN960A1S38S1dSd5A1VE;A2A3A2A2").
Definition s_fwc (msg len : Z) (C : axst) : wsub := ltac2:(tb__ "0|0|
SeeP1S3VC;A1S3Sb9Vmsg;Vlen;A2A1A3").

Definition fw_u1 (n : nat) : list nat := ltac2:(tb__ "0|2|
S17SeScSeU0ScSeU1S14SeA1M0A3A3S17SeSddU3M1Se3Vn;G1A2A2ScSeU2G0A3A3A3").
Definition fw_undo1 (T : axst) : axst := ltac2:(tb__ "0|0|
S16S1cS1fS3VT;A1A1A2SeS96Se3R1U1A2S37S3fR1A1VT;A2A2Tn;").
Definition fw_u2 (n : nat) : list nat := ltac2:(tb__ "0|1|
S17SeScSeU6ScSeU0S14SeA1A3A3S17SeSddU1U5A2SddU7M0Se3Vn;G0A2A2A3A3").
Definition fw_undo2L (U : axst) : axst := ltac2:(tb__ "0|1|
S16S1cS1fS3VU;A1A1A2SeS4dU0M0S37S3eR1A1Sc0Sb7VU;ScSb5Sb6G0A1S14Sb5A1A3A2VU;A2A2A2Tn;").
Definition fw_undo2M (U : axst) : axst := ltac2:(tb__ "0|0|
S16S1cS1fS3VU;A1A1A2SeS4dU0S37S3eR1A1VU;A2A2Tn;").

Definition E_oom : axst := Eval vm_compute in nthA G_cut LV_oom 0.
Lemma run_oom1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc2S11A5S10G0ScS4S9S41S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_oom : axst := Eval vm_compute in fw_siteM 0x14d77 19 E_oom.
Lemma oom_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS41S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S41A2M1A1U0M2S1dN960A1M3A3S10S20S3S39G2G3G1A3A1A2A3S1S0S13SdfS12S1eS1eA2S8SbaZ14d77M4Z13M5A2A1S6S41A1A3S11A3S0S2Sb0G4G5S41A3S52A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_oom : wsub := Eval vm_compute in s_fwc 0x14d77 19 C_oom.
Definition R_oom : list sobj := Eval vm_compute in optR (entails_frA C_oom (Pre_fw 0x14d77 19) s_oom).
Lemma fr_oom : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S52Sb9Z14d77Z13A2S7aA3S10G0S6aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_oom : ltac2:(tb__ "0|0|
S0S13Sd8S52Sb9Z14d77Z13A2S7aS6aSdcS4S2S7SbcA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_oom : axst := Eval vm_compute in T_after (Pre_fw 0x14d77 19) C_oom s_oom R_oom P_fw.
Definition U_oom : axst := Eval vm_compute in fw_undo1 T_oom.
Definition V_oom : axst := Eval vm_compute in fw_undo2M U_oom.
Lemma T_oom_eqs : ltac2:(tb__ "0|1|
S1S0S2SbfSb9Z14d77Z13A2S52S7aS6aSbbA5S58A3S1S0S2S40S58A1S5eA3S1S0SdS1cA1S1fS3S37S3fS16S1cS1fS3S58A1A1A2A1S58A2A1A1S17S1cS1fS3S5eA1A1M0S3dA3A3S1S0SfS20A1SdbS3S37S3eS16S1cG0A2A1S5eA2A1U0A2S10S20S3S70A1A2A3S0S2Sb1S5eA1S70A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition LV_xoom : list leafA := Eval vm_compute in runR 20 V_oom.
Lemma run_xoom : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS70S11A5S10G0S84A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xoom_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS84A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_oom : axst := Eval vm_compute in nthA V_oom LV_xoom 0.

Definition fp_rtc : list sobj := ltac2:(tb__ "0|0|
ScS1cSf6ScS1cSf5S14S1cA1A3A3").
Definition s_fpc (C : axst) : wsub := ltac2:(tb__ "0|0|
SeeP1S3VC;A1S3SebA1A3").
Definition fp_hints (C : axst) : list sprop := ltac2:(tb__ "0|1|
Se1S21S21S21SfS21A1SdS21A1Lx;SfaSb3VC;A1R1A2S21ScS21R1S14S21A1M0A3Lq;G0Xfx2Lp;ScS21Sf7Z918A1G0A3A4").

Definition ms16_at (b : sv) (d : Z) : sprop := ltac2:(tb__ "0|0|
S28S27Sf3S23Sf1S23Sf2S1dZ28A1S23Sf0Vb;S1dSe7Vd;A1A1A3A3S1dZfA1A3S1dZ0A1A3A1").
Definition fp_site (E : axst) : axst := ltac2:(tb__ "0|0|
S63S15S1eS1eS1dZ1a7c0A1S1dZ80A1A4S3cS75S39U0S1dNa80A1S38S1dSd5A1VE;A2A3A2A2S2SfbS97R1A1R1A2TC;").
Definition E_ref : axst := Eval vm_compute in nthA R1c LV_ref 0.
Lemma run_ref1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc4S11A5S10G0ScS4S9S43S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_ref : axst := Eval vm_compute in fp_site E_ref.
Lemma ref_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS43S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S43A2M1A1U0M2S1dNa80A1M3A3S10S20S3S39G2G3G1A3M4A1A2A3S1S0S13SdfS12S1eS1eA2S8S15S1eS1eS1dZ1a7c0A1S1dZ80A1A4M5A1S6S43A1A3S18A3S1S0S2SadS43A1S54A3S0SdS21A1S97S63G5S3cS75G4A2A2A1ScS21Sb2ScfZ998A2S14S21A1A3A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_ref : wsub := Eval vm_compute in s_fpc C_ref.
Definition R_ref : list sobj := Eval vm_compute in optR (entails_frA C_ref Pre_ref s_ref).
Lemma fr_ref : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S54SebS7cA3S10G0S6cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_ref : ltac2:(tb__ "0|0|
S0S13Sd8S54SebS7cS6cSdcS4S2S7SedA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_ref : axst := Eval vm_compute in T_after Pre_ref C_ref s_ref R_ref P_ref.

Definition fp_u1 (n : nat) : list nat := ltac2:(tb__ "0|2|
S17SeScSeU0ScSeU1ScSeU3ScSeU4S14SeA1M0A3A3A3A3S17SeSddU6M1Se3Vn;G1A2A2ScSeU2ScSeU5G0A3A3A3A3").
Definition fp_undo1 (T : axst) : axst := ltac2:(tb__ "0|0|
S16S1cS1fS3VT;A1A1A2SeS96Se3R1U2A2S37S98R1A1VT;A2A2Tn;").
Definition fp_u2 (n : nat) : list nat := ltac2:(tb__ "0|1|
S17SeScSeU7ScSeU0S14SeA1A3A3S17SeSddU1U6A2SddU8M0Se3Vn;G0A2A2A3A3").
Definition fp_undo2 (U : axst) : axst := ltac2:(tb__ "0|1|
S16S1cS1fS3VU;A1A1A2SeS4dU0M0S37S99R1A1Sc0Sb7VU;ScSb5Sb6G0A1S14Sb5A1A3A2VU;A2A2A2Tn;").
Definition U_ref : axst := Eval vm_compute in fp_undo1 T_ref.
Definition V_ref : axst := Eval vm_compute in fp_undo2 U_ref.
Lemma T_ref_eqs : ltac2:(tb__ "0|4|
S1S0S2SbfSebS54S7cS6cSecA5S5aA3S1S0S2SaeS5aA1S48A3S1S0SdS1cA1S1fS3S37S98S16S1cS1fS3S5aA1A1A2A1S5aA2A1A1S17S1cS1fS3S48A1A1M0S75A3A3S1S0SfS2A1Sb7S48ScSb5Sb6U0M1A1S14Sb5A1A3A2M2S10S2Sc0G2S48A2M3A2A3S1S0SfS20A1SdbS3S37S99S16S1cG0A2A1G3A2A1G1A2S10S20S3S71A1A2A3S0S2SafS48A1S71A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition LV_xref : list leafA := Eval vm_compute in runR 20 V_ref.
Lemma run_xref : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS71S11A5S10G0S86A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xref_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS86A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_ref : axst := Eval vm_compute in nthA V_ref LV_xref 0.

Definition fw_undoL (T : axst) : axst := ltac2:(tb__ "0|0|
S38ScbS4cS40VT;A1A1A2").

Definition fb_siteR (xb : sv * sv) (cap : sv) (F : axst) : axst := ltac2:(tb__ "0|0|
Sd1Vxb;Sd1S15S1eS1eSd3Vcap;A4VF;A2A2").
Definition s_fbR (cap : sv) (C : axst) : wsub := ltac2:(tb__ "0|1|
ScS12S32S1eA2M0S15S32S1ePfS1dSe7SceA1A1A4ScG0S15S32S1ePcSd3A4ScG0S15S32S1ePdVcap;A4SeeP1S3VC;A1S3ScaA1A3A3A3A3").

Definition E_sh1 : axst := Eval vm_compute in nthA R1c LV_sh1 0.
Lemma run_sh11 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc6S11A5S10G0ScS4S9S45S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_sh1 : axst := Eval vm_compute in fw_siteL 0x21441 31 E_sh1.
Lemma sh1_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS45S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S45A2M1A1U0M2S1dN9e0A1M3A3S10S20S3S39G2G3G1A3A1A2A3S1S0S13SdfS12S1eS1eA2S8SbaZ21441M4Z1fM5A2A1S6S45A1A3S18A3S0S2S65G4G5S45A3S56A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_sh1 : wsub := Eval vm_compute in s_fwc 0x21441 31 C_sh1.
Definition R_sh1 : list sobj := Eval vm_compute in optR (entails_frA C_sh1 (Pre_fw 0x21441 31) s_sh1).
Lemma fr_sh1 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S56Sb9Z21441Z1fA2S7eA3S10G0S6eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_sh1 : ltac2:(tb__ "0|0|
S0S13Sd8S56Sb9Z21441Z1fA2S7eS6eSdcS4S2S7SbcA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_sh1 : axst := Eval vm_compute in T_after (Pre_fw 0x21441 31) C_sh1 s_sh1 R_sh1 P_fw.
Definition U_sh1 : axst := Eval vm_compute in fw_undo1 T_sh1.
Definition V_sh1 : axst := Eval vm_compute in fw_undo2L U_sh1.
Definition W_sh1 : axst := Eval vm_compute in x4set vTP V_sh1.
Lemma T_sh1_eqs : ltac2:(tb__ "0|4|
S1S0S2SbfSb9Z21441Z1fA2S56S7eS6eSbbA5S5cA3S1S0S2S40S5cA1S4aA3S1S0SdS1cA1S1fS3S37S3fS16S1cS1fS3S5cA1A1A2A1S5cA2A1A1S17S1cS1fS3S4aA1A1M0S3dA3A3S1S0SfS2A1Sb7S4aScSb5Sb6U0M1A1S14Sb5A1A3A2M2S10S2Sc0G2S4aA2M3A2A3S1S0SfS20A1SdbS3S37S3eS16S1cG0A2A1G3A2A1G1A2S10S20S3S61A1A2A3S1S0S2S4cS4aA1S61A3S1S0S13S3aS61ScbA2S11A3S0S2S38ScbS61A2S90A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition LV_fsh1 : list leafA := Eval vm_compute in runR 20 W_sh1.
Lemma run_fsh1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS90S11A5S10G0S82A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_fsh1_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS82A1ScG0S15S31S33Sd6S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F_sh1 : axst := Eval vm_compute in nthA W_sh1 LV_fsh1 0.
Definition CF_sh1 : axst := Eval vm_compute in fb_siteR (xblk 0x21441 31) vCap F_sh1.
Lemma CF_sh1_eq : ltac2:(tb__ "0|0|
S0S2S64SbaZ21441Z1fA2Sd0Sa3A3S50A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sF_sh1 : wsub := Eval vm_compute in s_fbR vCap CF_sh1.
Definition RF_sh1 : list sobj := Eval vm_compute in optR (entails_frA CF_sh1 PreF sF_sh1).
Lemma frF_sh1 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S50ScaS78A3S10G0S68A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ccF_sh1 : ltac2:(tb__ "0|0|
S0S13Sd9S50ScaS78S68ScS2SccS14S2A1A3A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TF_sh1 : axst := Eval vm_compute in T_after PreF CF_sh1 sF_sh1 RF_sh1 PostF.
Lemma TF_sh1_eq : ltac2:(tb__ "0|0|
S0S2SbfScaS50S78S68SccA5S8cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition LV_xsh1 : list leafA := Eval vm_compute in runR 60 TF_sh1.
Lemma run_xsh1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U3cSbeS8cS11A5S10G0S88A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xsh1_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS88A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_sh1 : axst := Eval vm_compute in nthA W_sh1 LV_xsh1 0.

Definition E_ov1 : axst := Eval vm_compute in nthA R1c LV_ov1 0.
Lemma run_ov11 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc3S11A5S10G0ScS4S9S42S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_ov1 : axst := Eval vm_compute in fw_siteL 0x1609e 31 E_ov1.
Lemma ov1_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS42S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S42A2M1A1U0M2S1dN9e0A1M3A3S10S20S3S39G2G3G1A3A1A2A3S1S0S13SdfS12S1eS1eA2S8SbaZ1609eM4Z1fM5A2A1S6S42A1A3S18A3S0S2S65G4G5S42A3S53A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_ov1 : wsub := Eval vm_compute in s_fwc 0x1609e 31 C_ov1.
Definition R_ov1 : list sobj := Eval vm_compute in optR (entails_frA C_ov1 (Pre_fw 0x1609e 31) s_ov1).
Lemma fr_ov1 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S53Sb9Z1609eZ1fA2S7bA3S10G0S6bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_ov1 : ltac2:(tb__ "0|0|
S0S13Sd8S53Sb9Z1609eZ1fA2S7bS6bSdcS4S2S7SbcA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_ov1 : axst := Eval vm_compute in T_after (Pre_fw 0x1609e 31) C_ov1 s_ov1 R_ov1 P_fw.
Definition U_ov1 : axst := Eval vm_compute in fw_undo1 T_ov1.
Definition V_ov1 : axst := Eval vm_compute in fw_undo2L U_ov1.
Definition W_ov1 : axst := Eval vm_compute in x4set vTP V_ov1.
Lemma T_ov1_eqs : ltac2:(tb__ "0|4|
S1S0S2SbfSb9Z1609eZ1fA2S53S7bS6bSbbA5S59A3S1S0S2S40S59A1S47A3S1S0SdS1cA1S1fS3S37S3fS16S1cS1fS3S59A1A1A2A1S59A2A1A1S17S1cS1fS3S47A1A1M0S3dA3A3S1S0SfS2A1Sb7S47ScSb5Sb6U0M1A1S14Sb5A1A3A2M2S10S2Sc0G2S47A2M3A2A3S1S0SfS20A1SdbS3S37S3eS16S1cG0A2A1G3A2A1G1A2S10S20S3S5fA1A2A3S1S0S2S4cS47A1S5fA3S1S0S13S3aS5fScbA2S11A3S0S2S38ScbS5fA2S8eA3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition LV_fov1 : list leafA := Eval vm_compute in runR 20 W_ov1.
Lemma run_fov1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS8eS11A5S10G0S80A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_fov1_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS80A1ScG0S15S31S33Sd6S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F_ov1 : axst := Eval vm_compute in nthA W_ov1 LV_fov1 0.
Definition CF_ov1 : axst := Eval vm_compute in fb_siteR (xblk 0x1609e 31) vCap F_ov1.
Lemma CF_ov1_eq : ltac2:(tb__ "0|0|
S0S2S64SbaZ1609eZ1fA2Sd0Sa1A3S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sF_ov1 : wsub := Eval vm_compute in s_fbR vCap CF_ov1.
Definition RF_ov1 : list sobj := Eval vm_compute in optR (entails_frA CF_ov1 PreF sF_ov1).
Lemma frF_ov1 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S4eScaS76A3S10G0S66A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ccF_ov1 : ltac2:(tb__ "0|0|
S0S13Sd9S4eScaS76S66ScS2SccS14S2A1A3A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TF_ov1 : axst := Eval vm_compute in T_after PreF CF_ov1 sF_ov1 RF_ov1 PostF.
Lemma TF_ov1_eq : ltac2:(tb__ "0|0|
S0S2SbfScaS4eS76S66SccA5S8aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition LV_xov1 : list leafA := Eval vm_compute in runR 60 TF_ov1.
Lemma run_xov1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U3cSbeS8aS11A5S10G0S85A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xov1_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS85A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_ov1 : axst := Eval vm_compute in nthA W_ov1 LV_xov1 0.

Definition E_sh0 : axst := Eval vm_compute in nthA R1c LV_sh0 0.
Lemma run_sh01 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc5S11A5S10G0ScS4S9S44S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_sh0 : axst := Eval vm_compute in fw_siteL 0x21441 31 E_sh0.
Lemma sh0_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS44S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S44A2M1A1U0M2S1dN9e0A1M3A3S10S20S3S39G2G3G1A3A1A2A3S1S0S13SdfS12S1eS1eA2S8SbaZ21441M4Z1fM5A2A1S6S44A1A3S18A3S0S2S65G4G5S44A3S55A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_sh0 : wsub := Eval vm_compute in s_fwc 0x21441 31 C_sh0.
Definition R_sh0 : list sobj := Eval vm_compute in optR (entails_frA C_sh0 (Pre_fw 0x21441 31) s_sh0).
Lemma fr_sh0 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S55Sb9Z21441Z1fA2S7dA3S10G0S6dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_sh0 : ltac2:(tb__ "0|0|
S0S13Sd8S55Sb9Z21441Z1fA2S7dS6dSdcS4S2S7SbcA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_sh0 : axst := Eval vm_compute in T_after (Pre_fw 0x21441 31) C_sh0 s_sh0 R_sh0 P_fw.
Definition U_sh0 : axst := Eval vm_compute in fw_undo1 T_sh0.
Definition V_sh0 : axst := Eval vm_compute in fw_undo2L U_sh0.
Definition W_sh0 : axst := Eval vm_compute in x4set vTP V_sh0.
Lemma T_sh0_eqs : ltac2:(tb__ "0|4|
S1S0S2SbfSb9Z21441Z1fA2S55S7dS6dSbbA5S5bA3S1S0S2S40S5bA1S49A3S1S0SdS1cA1S1fS3S37S3fS16S1cS1fS3S5bA1A1A2A1S5bA2A1A1S17S1cS1fS3S49A1A1M0S3dA3A3S1S0SfS2A1Sb7S49ScSb5Sb6U0M1A1S14Sb5A1A3A2M2S10S2Sc0G2S49A2M3A2A3S1S0SfS20A1SdbS3S37S3eS16S1cG0A2A1G3A2A1G1A2S10S20S3S60A1A2A3S1S0S2S4cS49A1S60A3S1S0S13S3aS60ScbA2S11A3S0S2S38ScbS60A2S8fA3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition LV_fsh0 : list leafA := Eval vm_compute in runR 20 W_sh0.
Lemma run_fsh0 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS8fS11A5S10G0S81A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_fsh0_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS81A1ScG0S15S31S33Sd6S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F_sh0 : axst := Eval vm_compute in nthA W_sh0 LV_fsh0 0.
Definition CF_sh0 : axst := Eval vm_compute in fb_siteR (xblk 0x21441 31) vCap F_sh0.
Lemma CF_sh0_eq : ltac2:(tb__ "0|0|
S0S2S64SbaZ21441Z1fA2Sd0Sa2A3S4fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sF_sh0 : wsub := Eval vm_compute in s_fbR vCap CF_sh0.
Definition RF_sh0 : list sobj := Eval vm_compute in optR (entails_frA CF_sh0 PreF sF_sh0).
Lemma frF_sh0 : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S4fScaS77A3S10G0S67A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ccF_sh0 : ltac2:(tb__ "0|0|
S0S13Sd9S4fScaS77S67ScS2SccS14S2A1A3A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TF_sh0 : axst := Eval vm_compute in T_after PreF CF_sh0 sF_sh0 RF_sh0 PostF.
Lemma TF_sh0_eq : ltac2:(tb__ "0|0|
S0S2SbfScaS4fS77S67SccA5S8bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition LV_xsh0 : list leafA := Eval vm_compute in runR 60 TF_sh0.
Lemma run_xsh0 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U3cSbeS8bS11A5S10G0S87A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xsh0_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS87A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_sh0 : axst := Eval vm_compute in nthA W_sh0 LV_xsh0 0.

Definition E_shZ : axst := Eval vm_compute in nthA R1c LV_shZ 0.
Lemma run_shZ1 : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeSc7S11A5S10G0ScS4S9S46S34A2S14S4A1A3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_shZ : axst := Eval vm_compute in fw_siteL 0x21441 31 E_shZ.
Lemma shZ_pipe : ltac2:(tb__ "0|6|
S1S0S13S3aS46S1dSd5A1M0A2S11A3S1S0SfS20A1SdaS3S38G0S46A2M1A1U0M2S1dN9e0A1M3A3S10S20S3S39G2G3G1A3A1A2A3S1S0S13SdfS12S1eS1eA2S8SbaZ21441M4Z1fM5A2A1S6S46A1A3S18A3S0S2S65G4G5S46A3S57A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_shZ : wsub := Eval vm_compute in s_fwc 0x21441 31 C_shZ.
Definition R_shZ : list sobj := Eval vm_compute in optR (entails_frA C_shZ (Pre_fw 0x21441 31) s_shZ).
Lemma fr_shZ : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S57Sb9Z21441Z1fA2S7fA3S10G0S6fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_shZ : ltac2:(tb__ "0|0|
S0S13Sd8S57Sb9Z21441Z1fA2S7fS6fSdcS4S2S7SbcA4A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_shZ : axst := Eval vm_compute in T_after (Pre_fw 0x21441 31) C_shZ s_shZ R_shZ P_fw.
Definition U_shZ : axst := Eval vm_compute in fw_undo1 T_shZ.
Definition V_shZ : axst := Eval vm_compute in fw_undo2L U_shZ.
Definition W_shZ : axst := Eval vm_compute in x4set vTP V_shZ.
Lemma T_shZ_eqs : ltac2:(tb__ "0|4|
S1S0S2SbfSb9Z21441Z1fA2S57S7fS6fSbbA5S5dA3S1S0S2S40S5dA1S4bA3S1S0SdS1cA1S1fS3S37S3fS16S1cS1fS3S5dA1A1A2A1S5dA2A1A1S17S1cS1fS3S4bA1A1M0S3dA3A3S1S0SfS2A1Sb7S4bScSb5Sb6U0M1A1S14Sb5A1A3A2M2S10S2Sc0G2S4bA2M3A2A3S1S0SfS20A1SdbS3S37S3eS16S1cG0A2A1G3A2A1G1A2S10S20S3S62A1A2A3S1S0S2S4cS4bA1S62A3S1S0S13S3aS62ScbA2S11A3S0S2S38ScbS62A2S91A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition LV_fshZ : list leafA := Eval vm_compute in runR 20 W_shZ.
Lemma run_fshZ : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U14SbeS91S11A5S10G0S83A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_fshZ_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS83A1ScG0S15S31S33Sd6S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F_shZ : axst := Eval vm_compute in nthA W_shZ LV_fshZ 0.
Definition CF_shZ : axst := Eval vm_compute in fb_siteR (xblk 0x21441 31) (SLit CAP0) F_shZ.
Lemma CF_shZ_eq : ltac2:(tb__ "0|0|
S0S2S64SbaZ21441Z1fA2S1dSf4A1Sa4A3S51A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sF_shZ : wsub := Eval vm_compute in s_fbR (SLit CAP0) CF_shZ.
Definition RF_shZ : list sobj := Eval vm_compute in optR (entails_frA CF_shZ PreF sF_shZ).
Lemma frF_shZ : ltac2:(tb__ "0|1|
S0SfSdS1cA1M0A1Sd7S51ScaS79A3S10G0S69A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ccF_shZ : ltac2:(tb__ "0|0|
S0S13Sd9S51ScaS79S69ScS2SccS14S2A1A3A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TF_shZ : axst := Eval vm_compute in T_after PreF CF_shZ sF_shZ RF_shZ PostF.
Lemma TF_shZ_eq : ltac2:(tb__ "0|0|
S0S2SbfScaS51S79S69SccA5S8dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition LV_xshZ : list leafA := Eval vm_compute in runR 60 TF_shZ.
Lemma run_xshZ : ltac2:(tb__ "0|1|
S0SfSdS4A1M0A1S5Sb8U3cSbeS8dS11A5S10G0S89A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LV_xshZ_pcs : ltac2:(tb__ "0|1|
S0SdS12S31S33A2M0A1S3bS89A1ScG0S15S31S33Se4S34A4S14G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_shZ : axst := Eval vm_compute in nthA W_shZ LV_xshZ 0.

Definition lc_objR (c : Z * Z * list (Z * nat * Z)) : sobj := ltac2:(tb__ "0|5|
S12S12S31S31A2M0SdS12S12S31SeA2M1S31A2M2A1M3A2S1cLc;Vc;G0G3G0S1cLp;R2S31S31SffS1dZ0A1R2R1SdcG2S12G1S1eA2M4G2G2G4Lc;R1G1S31G1G4Ly;R2S31SeS15G1S1eS15S31SeR2R1A4S1dR3A1A4Lk;La;X12x1Lv;Ly;X12x1Lc;R3A4A4Lhi;Llo;X12x1Lcs;Lp;X12x1").
Definition ex_carvedR : list sobj := map lc_objR N_ex.

Definition ex_img (A : axst) : axst := ltac2:(tb__ "0|1|
ScdS1fS3VA;A1M0A1S1dZ0A1S1dSe5A1A3SeSaVA;SfdG0R1Se8Se5Z8cA2Z4SeaSe9Z2Z20A2Z1A2A5A2Tie;").
Definition ex_img_okb (A : axst) : bool := ltac2:(tb__ "0|1|
ScdS1fS3VA;A1M0A1S1dZ0A1S1dSe5A1A3SeSfeSb8G0R1Se8Se5Z8cA2Z4SeaSe9Z2Z20A2Z1A2A6Tie;").

Definition ex_fin (A : axst) : axst := ltac2:(tb__ "0|1|
SefS38S1dSd5A1S3cS73S74SefVA;S14S12S1eS1eA2A1M0A2A1A2A2G0A2").

Definition ex_siteD (cut : Z) (E : axst) : axst := ltac2:(tb__ "0|0|
S93S39U0S1dVcut;A1VE;A3A1").

Definition exS_rb (E : axst) : axst := ltac2:(tb__ "0|0|
ScdS1fS3VE;A1A1Sd2S1dSe7SceA1A1A3SeSc0Sb7VE;ScSb5Sb6R1A1S14Sb5A1A3A2VE;A2Tiw;").
Definition exS_idxs (E1 : axst) : list nat := ltac2:(tb__ "0|2|
S1fS3VE1;A1A1SdS1cA1S16S1cR1A2SeScdR2ScfS1dSe7Se8SceZ80A2A1A1A3SeScdR3ScfS1dN80A1A3SeS17SeScSeR2ScSeR1S14SeA1M0A3A3S102SeSdSeA1S104SeA1SeS101S1aSdfSeS100R1A1ScSeR3ScSeR2G0A3A3A3A1M1A1Li;SeS103G1A1Lx;SddU0R3A2A6A3Tim;Tiw;Tn;Tobjs;").
Definition ex_siteS (E : axst) : axst := ltac2:(tb__ "0|1|
S92VE;A1S2S93S39U0M0S1dN430A1S4dG0S37S72R1A1R1A2A2A3A1TE1;").

Definition s_exR (w : Z) (C : axst) : wsub := ltac2:(tb__ "0|2|
S17S12S32S1eA2M0ScG0S15S32S1eP11S1dVw;A1A4ScG0S15S32S1eP12S1dZ0M1A1A4S14G0A1A3A3Sd4VC;G1Z2A3A3").
Definition exR (w : Z) (C : axst) : list sobj := ltac2:(tb__ "0|0|
Sc9Sd7VC;Se6Z0Z2A2S9aVw;VC;A2A3A1").
Definition ex_okb (w : Z) (C : axst) : bool := ltac2:(tb__ "0|4|
SfSdS1cA1M0A1S13Lx;Sd7VC;Se6Z0Z2A2M1S9aVw;VC;A2M2A3G0S19Sd8VC;G1G2R1S14S2A1A5Se2S21S2aS25S3VC;A1M3A1A1S24G3A1A3A2LR;S18Xfx2").

Definition CX_oom : axst := Eval vm_compute in ex_siteD (-1024) X_oom.
Definition CX_ref : axst := Eval vm_compute in ex_siteD (-1152) X_ref.
Definition CX_sh1 : axst := Eval vm_compute in ex_siteS X_sh1.
Definition CX_ov1 : axst := Eval vm_compute in ex_siteS X_ov1.
Definition CX_sh0 : axst := Eval vm_compute in ex_siteS X_sh0.
Definition CX_shZ : axst := Eval vm_compute in ex_siteS X_shZ.
Lemma exD_pipe : ltac2:(tb__ "0|4|
S12S12S12S2S31A2M0S31A2M1S2A2M2Se0G2R1ScG2S15G1S2S15G0S31S15S2S31Sa5N400A4SbdA4S9bA4ScG2S15G1S2S15G0S31S15S2S31Sa7N480A4Z0A4S9dA4S14G2A1A3A3A3G2OLp;R2G1S2G1OLp0;R2G0S31G0OLp1;R2S2S31S39U0M3S1dR1A1R2A3S2S74R1A1S2S3cS73R1A2S2S1S0SfS20A1SdaS3R5A1G3S1dR4A1A3S10S20S3R3A1A2A3S1S0S13S94R3A1S11A3S1S0S13S3aR1S1dSd5A1A2S11A3S1S0S2SabR4R5A2R8A3S0S13S95R6R8A2S11A3A2A2A2A2TA3;TA2;TA1;Lcut;LE;X12x1Lw;Lp1;X12x1LC;Lp0;X12x1F_;Fp;").
Proof. intros p Hp. repeat (destruct Hp as [<-|Hp]; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2|]). destruct Hp. Qed.
Lemma exS_pipe : ltac2:(tb__ "0|5|
S12S2S2A2M0Se0G0R1ScG0S15S2S2Sa9S9fA4ScG0S15S2S2Sa6S9cA4ScG0S15S2S2Sa8S9eA4ScG0S15S2S2SaaSa0A4S14G0A1A3A3A3A3A3G0OLp;R2S2S2ScdS1fS3R2A1A1Sd2S1dSe7SceA1A1A3SeS92R3A1S2S37S72R1A1R1A2S2S4dU0M1R1A2S2S39G1S1dN430A1M2R1A3S2S74R1A1S2S3cS73R1A2S2S1S0SfS2A1Sb7R9ScSb5Sb6R7A1S14Sb5A1A3A2S10S2R6A2A3S1S0S13SfcS16S1cS1fS3R6A1A1A2S72R6A1A2S11A3S1S0SfS20A1M3SdbS3R5A1G1A2S10S20S3R4A1M4A2A3S1S0G3SdaG4G1G2A3S10S20S3R3A1A2A3S1S0S13S94R3A1S11A3S1S0S13S3aR1S1dSd5A1A2S11A3S1S0S2SacR9A1R8A3S0S13S95SbdR8A2S11A3A2A2A2A2A2A2A2TA3;TA2;TA1;TA0';TA0;TE1;Tiw;LC;LE;X12x1F_;Fp;").
Proof. intros p Hp. repeat (destruct Hp as [<-|Hp]; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2|]). destruct Hp. Qed.
End DrvR_tstates.

(* [comment removed for export] *)
Module DrvTLXi_h.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition optS'' := 0.
Definition optS' (x : option sstate) (d : sstate) : sstate := match x with Some s => s | None => d end.
Definition optA (x : option axst) (d : axst) : axst := match x with Some s => s | None => d end.
End DrvTLXi_h.

