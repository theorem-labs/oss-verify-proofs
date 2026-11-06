(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_042.   (* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From Stdlib Require NArith PArith Lia FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From Stdlib Require Permutation.

(* [comment removed for export] *)
Module SegQS_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "bool"; "pair"; "prod"; "nil"; "list"; "app"; "true"; "length"; "false"; "option"; "Some"; "andb"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "ss_next"; "SPUle"; "valuation"; "SAlu"; "ss_lenient"; "SPBranch"; "ss_facts"; "SPNot"; "SPUlt"; "SVar"; "ss_objs"; "sv_eqb"; "SPAlign"; "ob_base"; "ob_hi"; "ob_lo"; "sprop_below"; "DUnknown"; "agree_below"; "cell"; "mkObj"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "vmap"; "chkNM"; "keepsM"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "vH"; "C5"; "vMS"; "T5f"; "SC"; "vNCH"; "AM"; "AU"; "EM"; "EU"; "GBEXIT"; "GBSCAN"; "S0"; "SX"; "s5"; "D_M"; "D_U"; "R5"; "T5of"; "VSX"; "dropk"; "MSENTS"; "O_clast"; "O_hidx"; "VS0"; "cntD"; "idxs_of"; "isin"; "runPA"; "runPB"; "runPC"; "runPD"; "runPE"; "runPL"; "selX"; "sel_last"; "setpc"; "vIDX"; "vPAB"; "vPTR"; "E5"; "EMd"; "EMx"; "EUd"; "EUx"; "LA"; "LENS"; "O_cidx"; "O_csh"; "O_hh"; "O_ihdr"; "O_lidx"; "O_secg"; "O_secm"; "O_secn"; "O_secs"; "O_stS"; "TOPMAX"; "TsPA"; "TsPB"; "TsPC"; "TsPD"; "TsPE"; "TsPL"; "addos"; "dropD"; "jregs"; "vEND"; "vLAST"; "AM_0_L"; "AM_0_M"; "AM_1_L"; "AM_1_M"; "AM_2_L"; "AM_2_M"; "AU_0_L"; "AU_0_M"; "AU_1_L"; "AU_1_M"; "AU_2_L"; "AU_2_M"; "BSHS"; "C5_0_L"; "C5_0_M"; "C5_1_L"; "C5_1_M"; "C5_2_L"; "C5_2_M"; "E5_0_L"; "E5_0_M"; "E5_1_L"; "E5_1_M"; "E5_2_L"; "E5_2_M"; "EM_0_L"; "EM_0_M"; "EM_1_L"; "EM_1_M"; "EM_2_L"; "EM_2_M"; "EMd_0_L"; "EMd_0_M"; "EMd_1_L"; "EMd_1_M"; "EMd_2_L"; "EMd_2_M"; "EMx_0_L"; "EMx_0_M"; "EMx_1_L"; "EMx_1_M"; "EMx_2_L"; "EMx_2_M"; "EU_0_L"; "EU_0_M"; "EU_1_L"; "EU_1_M"; "EU_2_L"; "EU_2_M"; "EUd_0_L"; "EUd_0_M"; "EUd_1_L"; "EUd_1_M"; "EUd_2_L"; "EUd_2_M"; "EUs"; "EUs_0_L"; "EUs_0_M"; "EUs_1_L"; "EUs_1_M"; "EUs_2_L"; "EUs_2_M"; "EUx_0_L"; "EUx_0_M"; "EUx_1_L"; "EUx_1_M"; "EUx_2_L"; "EUx_2_M"; "F1"; "F2"; "F_h"; "F_len"; "F_m"; "LA_0"; "LA_1"; "LA_2"; "LL"; "LL_0"; "LL_1"; "LL_2"; "LR"; "LR_0_L"; "LR_0_M"; "LR_1_L"; "LR_1_M"; "LR_2_L"; "LR_2_M"; "OBJ1"; "OBJ2"; "O_cfbS"; "O_cftS"; "O_chS"; "O_pgbS"; "O_seci"; "SC_0"; "SC_1"; "SC_2"; "SX_0_L"; "SX_0_M"; "SX_1_L"; "SX_1_M"; "SX_2_L"; "SX_2_M"; "T5f_0_L"; "T5f_0_M"; "T5f_1_L"; "T5f_1_M"; "T5f_2_L"; "T5f_2_M"; "VSC"; "rtiS"; "vCHV"; "vLIDX"; "vNEAR"; "vNhi"; "vNlo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "runA"; "NPRE"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "@Stdlib.Lists.List"; "In"; "forallb";
"@Stdlib.PArith.BinPos.Pos"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "vIT"; "QIRET2"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "ALU_SRL"; "ALU_SLL"; "ALU_SUB"; "BC_LTU"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "addf"; "addo"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vCTX"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "DQI0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states"; "optR"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition GBSCAN : Z := 0x3e8c0.
Definition GBEXIT : Z := 0x3e8ec.
Definition MSENTS : Z := 0xde378.
Definition TOPMAX : Z := 140737479966720.
Definition vPAB := SVar 200. Definition vNCH := SVar 201. Definition vH := SVar 202. Definition vMS := SVar 203. Definition vIDX := SVar 204.
Definition vLAST := SVar 205. Definition vLIDX := SVar 206. Definition vNhi := SVar 207. Definition vNlo := SVar 209.
Definition vPTR := SVar 210. Definition vCHV := SVar 211. Definition vNEAR := SVar 212. Definition vEND := SVar 213.

Definition O_seci : sobj := ltac2:(tb__ "0|3|
Sf5S19Z0A1SfdS10bSfdZ10A2S1S4S4S14S0A2M0S16A2M1S3G0S16S3S14S0SfdU8M2A4S19S11bA1A4S1G1S3G0S16S3S14S0S10bSfdZ8A2G2A4S60A4S5G1A1A3A3A4").
Definition O_secn : sobj := ltac2:(tb__ "0|3|
Sf5S19Z0A1S10bSfdZ38A2M0S10bSfdZ40A2S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4S3fA4S5G2A1A3A4").
Definition O_secs : sobj := ltac2:(tb__ "0|0|
Sf5S19Z0A1S10bSfdZ40A2Zee040S5S4S4S14S0A2S16A2A1A4").
Definition O_secm : sobj := ltac2:(tb__ "0|4|
Sf5S19Z0A1M0Zee040M1Zee044S1S4S4S14S0A2M2S16A2M3S3G2S16S3S14S0G1U4A4G0A4S5G3A1A3A4").
Definition O_secg : sobj := carved (SLit 0) 0xee048 0xee070 [].
Definition O_cftS : sobj := ltac2:(tb__ "0|3|
Sf5S19Z0A1Z182fa0M0Z182fa8S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4S19ZffffffffffffffffA1A4S5G2A1A3A4").
Definition O_cfbS : sobj := ltac2:(tb__ "0|4|
Sf5S19Z0A1M0Z182fb8M1Z182fc0S1S4S4S14S0A2M2S16A2M3S3G2S16S3S14S0G1U8A4G0A4S5G3A1A3A4").
Definition O_pgbS : sobj := ltac2:(tb__ "0|3|
Sf5S19Z0A1Z180ea0M0Z180ea8S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4S19S11bA1A4S5G2A1A3A4").
Definition O_stS : sobj := carved vT 2768 3168 [].
Definition O_ihdr : sobj := ltac2:(tb__ "0|3|
Sf5S109Z2M0Z8S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U2A4Sf1A4S1G2S3G1S16S3S14S0Z4U4A4Sf2A4S5G2A1A3A3A4").
Definition O_chS (b v : sv) : sobj := ltac2:(tb__ "0|3|
Sf5Vb;Z0M0Z8S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4Vv;A4S5G2A1A3A4").
Definition O_hh (h ms : sv) : sobj := ltac2:(tb__ "0|4|
Sf5Vh;Z0M0Z10S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8M3A4Vh;A4S1G2S3G1S16S3S14S0Z8G3A4Vms;A4S5G2A1A3A3A4").
Definition O_hidx (h v : sv) : sobj := ltac2:(tb__ "0|3|
Sf5Vh;Z18M0Z20S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4Vv;A4S5G2A1A3A4").
Definition BSHS (h : sv) : sv := ltac2:(tb__ "0|0|
Sf9S1dS110Vh;S19Z3A1A3S19Z7fff8000A1A2").
Definition LENS (ms : sv) : sv := SAlu ALU_SRL ms (SLit 3).
Definition O_csh (h ms : sv) : sobj := ltac2:(tb__ "0|0|
S2eS8bVh;A1S19Z0A1S68Vms;A1S5S2dA1S2bA5").
Definition O_cidx (h : sv) : sobj := ltac2:(tb__ "0|3|
Sf5Sf9S60S1dS111S5fS19Z3A1A3A2Z0M0Z8S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4Vh;A4S5G2A1A3A4").
Definition O_clast (v : sv) : sobj := ltac2:(tb__ "0|3|
Sf5Sf9S1dS111S3fS19Z3A1A3S60A2N8M0Z0S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4Vv;A4S5G2A1A3A4").
Definition O_lidx : sobj := ltac2:(tb__ "0|3|
Sf5S7eZ18M0Z20S1S4S4S14S0A2M1S16A2M2S3G1S16S3S14S0G0U8A4SefA4S5G2A1A3A4").
Definition rtiS : list sobj := map carve_obj N_rti.
Definition OBJ1 : list sobj := ltac2:(tb__ "0|0|
S7S17SedS1S17SdcS1S17S70S1S17S71S1S17S6fS1S17S6eS1S17Sd9S1S17Sd8S1S17SdbS1S17S72S1S17S6cS5S17A1A3A3A3A3A3A3A3A3A3A3A3").
Definition OBJ2 (l : bool) (h : sv) : list sobj := ltac2:(tb__ "0|1|
S7S17S1S17S6aVh;S3cA2S1S17S6bVh;S3cA2S5S17A1M0A3A3S2S6S17A1Ll;Vl;S1S17S51Vh;Sf9S3fS19N1A1A2A2S1S17S50Vh;A1G0A3A3S1S17S51Vh;S5fA2S1S17S69Vh;A1S1S17S50S7eA1S1S17S6dG0A3A3A3A3X2x2A3").
Definition addos (X : axst) (os : list sobj) : axst := fold_left addo os X.
Definition setpc (X : axst) (pc : Z) (ru : list (nat * sv)) : axst := ltac2:(tb__ "0|0|
S10VX;A1S34S12VX;S2fVpc;S121S32R1A1Vru;A2S31R1A1S30R1A1S33R1A1S24R1A1S20R1A1S1aR1A1S1eR1A1A9A2TS;").
Definition dropk (X : axst) (k : nat) : axst := ltac2:(tb__ "0|2|
S12VX;S123S10VX;A1M0S115S17S11fS9S17S24G0A1M1A2Vk;A2G1A3A2A2").

Definition same_rngS (o o' : sobj) : bool := ltac2:(tb__ "0|0|
SdSdS25S27Vo;A1S27Vo';A1A2S25S29Vo;A1S29Vo';A1A2A2S25S28Vo;A1S28Vo';A1A2A2").
Definition isin (D : list sobj) (o : sobj) : bool := existsb (same_rngS o) D.
Fixpoint idxs_of (p : sobj -> bool) (l : list sobj) (i : nat) : list nat :=
  match l with [] => [] | o :: r => (if p o then [i] else []) ++ idxs_of p r (S i) end.
Definition sel_last (X : axst) (D : list sobj) : list nat := ltac2:(tb__ "0|2|
S7S0S54S17SeS55VD;R1A2A1Lo;S24S10VX;A1A1M0U0M1A3S54S55VD;A1G0G1A3A3").
Definition selX (X : axst) (D : list sobj) : axst := ltac2:(tb__ "0|0|
SbSfA1SfLx;S107VX;S1S105S106S5dVX;VD;A2A1S5S105A1A3A2SfR1LY;VX;Xbx2").
Definition cntD (X : axst) (D : list sobj) : nat := ltac2:(tb__ "0|0|
S9S0S54S55VD;A1S24S10VX;A1A1U0A3A2").
Definition dropD (X : axst) (D : list sobj) : axst := ltac2:(tb__ "0|0|
S4eS5cVX;VD;A2S53VX;VD;A2A2").

Definition F_m (f : nat) : list sprop := ltac2:(tb__ "0|3|
S0S6S18A1M0Lf;Vf;S1S18S22S109SfcA2S5S18A1M1A3M2S0S0G0Ln;R1G2S0S1S18S1bSf9SfcS19S10cZ2Z25A2A1A2S109A2G1A3Ln0;X0x2Ln;X0x2").
Definition F1 (f : nat) : list sprop := ltac2:(tb__ "0|2|
S7S18Sc7Vf;A1S1S18S1bS19S11cA1SfcA2S1S18S1bSfcS19S10dS10dS73S10cZ2M0Z25A2A2Z1000A2A1A2S1S18S21S1fS10eS3fS19Z0A1M1A3A1S1S18S1bS3fS19S10cG0Z14A2A1A2S1S18S21S1fS10eS126G1A3A1S1S18S21S1fS10eS125G1A3A1S5S18A1A3A3A3A3A3A3A3").

Definition F_h (f : nat) : list sprop := ltac2:(tb__ "0|6|
S0S6S18A1M0Lf;Vf;S1S18S1bSf9S3aS3cA2S19Z7fff7000A1M1A2S1S18S1bSf9S3cS3aA2G1A2S1S18S22Sf9S3aS19Z1000A1A2M2SfcA2S5S18A1M3A3M4A3A3S0S0G0Ln;R1S1S18S1bS19Z10007fff8000A1S3aA2M5G4A3S0S1S18G5S1S18S1bSf9SfcS19S10cZ2Z25A2A1A2G2A2G3A3A3Ln0;X0x2Ln;X0x2").

Definition F_len : sprop := ltac2:(tb__ "0|1|
S1fS113S1dS112S1dS10fS1dS110S1dS10fS1dS10fS3aS3cA3S19N8A1A3S19Z3A1M0A3S19Z1A1A3S1dS110S3aG0A3A3S19ZffffffffffffffffA1A3").
Definition F2 (f : nat) (l : bool) : list sprop := ltac2:(tb__ "0|4|
S7S18S1S18Sc6S1S18S21S1fS10eS3aS19Z0A1A3A1S1S18S1bS3aS109A2S1S18S22S109Sf9S3aS3cA2M0A2S1S18S26PcaZcM1A2S1S18S26PcbG1A2S1S18S1bS19Z12000A1S3cA2S1S18S1bS3cS19S73A1M2A2S1S18S1bS19Z646000A1S3aA2S1S18S1bG0G2A2S1S18S1bSf9S3cS3aA2G2A2S5S18A1M3A3A3A3A3A3A3A3A3A3A3A3S7S18Sc5Vf;A1S2S6S18A1Ll;Vl;G3S1S18S22S5fSf9S3fS19N1A1A2A2G3A3X2x2A3A3").
Definition jregs : list (nat * sv) := ltac2:(tb__ "0|1|
S1S4S0S16A2M0S3S0S16UfS23Pc0A1A4S1G0S3S0S16U10S23Pc1A1A4S1G0S3S0S16U11S23Pc2A1A4S1G0S3S0S16U5S23PacA1A4S5G0A1A3A3A3A3").

Definition S0 (f : nat) : axst := ltac2:(tb__ "0|0|
S11dS7aS127Sd6A2Sc3Vf;A1A2").
Definition runPA (f : nat) : list leafA := ltac2:(tb__ "0|0|
SfaU12cS1S14S45S1S14S44S5S14A1A3A3S46Vf;A1A3").
Lemma runPA_eq : ltac2:(tb__ "0|0|
S0S38S6S11A1SfaU12cS1S14S45S1S14S44S5S14A1A3A3S46R1A1A3S56R1A1A3Ff;"). Proof. intros f. unfold runPA. reflexivity. Qed.
Definition LA_0 : axst := Eval vm_compute in (leaf 0 (runPA 0)).
Definition LA_1 : axst := Eval vm_compute in (leaf 0 (runPA 1)).
Definition LA_2 : axst := Eval vm_compute in (leaf 0 (runPA 2)).
Definition LA (f : nat) : axst := ltac2:(tb__ "0|0|
S0SfLf;Vf;Sc8S0S0SfLn;R1Sc9S0ScaLn0;X0x2Ln;X0x2").
Definition VS0 : list positive := ltac2:(tb__ "0|0|
S1S15Pa0S1S15Pa1S1S15Pa2S1S15Pa3S1S15Pa4S1S15Pa5S1S15Pa6S1S15Pb8S1S15Pb9S1S15PbaS1S15PbbS1S15Pd0S1S15Pc8S1S15Pc9S1S15PcfS1S15Pd1S5S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition TsPA (f : nat) : list (axst * vmap) := ltac2:(tb__ "0|1|
S1S4SfS35A2M0S3SfS35S67Vf;A1S108S52A1A4S5G0A1A3").

Definition SCof (f : nat) : axst := ltac2:(tb__ "0|1|
S11eS5eS67Vf;A1S45S7S4S0S16A2M0S1G0S3S0S16UcS61A4S1G0S3S0S16UdSf0A4S1G0S3S0S16UeS7dA4S5G0A1A3A3A3S7cA3A3SdaS61SeeA2A2").
Definition SC_0 : axst := Eval vm_compute in (SCof 0).
Definition SC_1 : axst := Eval vm_compute in (SCof 1).
Definition SC_2 : axst := Eval vm_compute in (SCof 2).
Definition SC (f : nat) : axst := ltac2:(tb__ "0|0|
S0SfLf;Vf;SddS0S0SfLn;R1SdeS0SdfLn0;X0x2Ln;X0x2").
Definition runPL (f : nat) : list leafA := ltac2:(tb__ "0|0|
SfaU64S1S14S45S1S14S44S5S14A1A3A3S3eVf;A1A3").
Lemma runPL_eq : ltac2:(tb__ "0|0|
S0S38S6S11A1SfaU64S1S14S45S1S14S44S5S14A1A3A3S3eR1A1A3S5bR1A1A3Ff;"). Proof. intros f. unfold runPL. reflexivity. Qed.
Definition LL_0 : list axst := Eval vm_compute in (map la_state (runPL 0)).
Definition LL_1 : list axst := Eval vm_compute in (map la_state (runPL 1)).
Definition LL_2 : list axst := Eval vm_compute in (map la_state (runPL 2)).
Definition LL (f : nat) : list axst := ltac2:(tb__ "0|1|
S0S6SfA1M0Lf;Vf;SccS0S0G0Ln;R1ScdS0SceLn0;X0x2Ln;X0x2").
Definition VSC : list positive := ltac2:(tb__ "0|0|
S7S15S52S1S15Pd2S1S15Pd3S1S15Pd4S1S15Pd5S1S15Pc0S1S15Pc1S1S15Pc2S1S15PacS5S15A1A3A3A3A3A3A3A3A3A3").
Definition TsPL (f : nat) : list (axst * vmap) := ltac2:(tb__ "0|0|
S114SfS4SfS35A2SfS3SfS35R1S108SecA1A4LT;ScbVf;A1A4").

Definition SXof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S11dS7aS4eS5eS3eVf;A1S44S7S4S0S16A2M0S1G0S3S0S16UcS61A4S1G0S3S0S16UdS3aA4S1G0S3S0S16UeS7dA4S5G0A1A3A3A3S7cA3A3U1A2Sd7Vl;S3aA2A2Sc4Vf;Vl;A2A2").
Definition SX_0_L : axst := Eval vm_compute in (SXof 0 true).
Definition SX_0_M : axst := Eval vm_compute in (SXof 0 false).
Definition SX_1_L : axst := Eval vm_compute in (SXof 1 true).
Definition SX_1_M : axst := Eval vm_compute in (SXof 1 false).
Definition SX_2_L : axst := Eval vm_compute in (SXof 2 true).
Definition SX_2_M : axst := Eval vm_compute in (SXof 2 false).
Definition SX (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Se0Se1X2x2S0S0SfLn;R1G0Vl;Se2Se3X2x2S0G0Vl;Se4Se5X2x2Ln0;X0x2Ln;X0x2").
Definition runPB (f : nat) (l : bool) : list leafA := ltac2:(tb__ "0|0|
SfaU384S1S14S4fS5S14A1A3S47Vf;Vl;A2A3").
Lemma runPB_eq : ltac2:(tb__ "0|0|
S0S2S38S6S11A1SfaU384S1S14S4fS5S14A1A3S47R2R1A2A3S57R2R1A2A3Fl;Ff;"). Proof. intros f l. unfold runPB. reflexivity. Qed.
Definition E5_0_L : axst := Eval vm_compute in (leaf 0 (runPB 0 true)).
Definition E5_0_M : axst := Eval vm_compute in (leaf 0 (runPB 0 false)).
Definition E5_1_L : axst := Eval vm_compute in (leaf 0 (runPB 1 true)).
Definition E5_1_M : axst := Eval vm_compute in (leaf 0 (runPB 1 false)).
Definition E5_2_L : axst := Eval vm_compute in (leaf 0 (runPB 2 true)).
Definition E5_2_M : axst := Eval vm_compute in (leaf 0 (runPB 2 false)).
Definition E5 (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S92S93X2x2S0S0SfLn;R1G0Vl;S94S95X2x2S0G0Vl;S96S97X2x2Ln0;X0x2Ln;X0x2").
Definition VSX (l : bool) : list positive := ltac2:(tb__ "0|1|
S7S15S52S7S15S1S15PcaS1S15PcbS1S15Pd2S1S15Pd5S1S15Pc0S1S15Pc1S1S15Pc2S1S15PacS5S15A1M0A3A3A3A3A3A3A3A3S2S6S15A1Ll;Vl;G0S1S15PccS1S15PcdS1S15PceG0A3A3A3X2x2A3A3").
Definition TsPB (f : nat) (l : bool) : list (axst * vmap) := ltac2:(tb__ "0|1|
S1S4SfS35A2M0S3SfS35S62Vf;Vl;A2S108S4dVl;A1A1A4S5G0A1A3").

Definition C5of (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S5eS62Vf;Vl;A2S4fS1S4S0S16A2M0S3S0S16UcS68S3cA1A4S5G0A1A3A3").
Definition C5_0_L : axst := Eval vm_compute in (C5of 0 true).
Definition C5_0_M : axst := Eval vm_compute in (C5of 0 false).
Definition C5_1_L : axst := Eval vm_compute in (C5of 1 true).
Definition C5_1_M : axst := Eval vm_compute in (C5of 1 false).
Definition C5_2_L : axst := Eval vm_compute in (C5of 2 true).
Definition C5_2_M : axst := Eval vm_compute in (C5of 2 false).
Definition C5 (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S8cS8dX2x2S0S0SfLn;R1G0Vl;S8eS8fX2x2S0G0Vl;S90S91X2x2Ln0;X0x2Ln;X0x2").
Definition s5 (f : nat) (l : bool) : wsub := ltac2:(tb__ "0|0|
S122P1S10S3bVf;Vl;A2A1S10S102A1A3").
Definition R5 (f : nat) (l : bool) : list sobj := ltac2:(tb__ "0|0|
S128S117S3bVf;Vl;A2S102S48Vf;Vl;A2A3A1").
Definition T5of (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S118S48Vf;Vl;A2S102S120S124S104A1A1S3bVf;Vl;A2S4bVf;Vl;A2A5").
Definition T5fof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S116S4cVf;Vl;A2S20S10S3bVf;Vl;A2A1A1A2").
Definition T5f_0_L : axst := Eval vm_compute in (T5fof 0 true).
Definition T5f_0_M : axst := Eval vm_compute in (T5fof 0 false).
Definition T5f_1_L : axst := Eval vm_compute in (T5fof 1 true).
Definition T5f_1_M : axst := Eval vm_compute in (T5fof 1 false).
Definition T5f_2_L : axst := Eval vm_compute in (T5fof 2 true).
Definition T5f_2_M : axst := Eval vm_compute in (T5fof 2 false).
Definition T5f (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Se6Se7X2x2S0S0SfLn;R1G0Vl;Se8Se9X2x2S0G0Vl;SeaSebX2x2Ln0;X0x2Ln;X0x2").

Definition runPC (f : nat) (l : bool) : list leafA := ltac2:(tb__ "0|0|
SfaU384S5S14A1S3dVf;Vl;A2A3").
Lemma runPC_eq : ltac2:(tb__ "0|0|
S0S2S38S6S11A1SfaU384S5S14A1S3dR2R1A2A3S58R2R1A2A3Fl;Ff;"). Proof. intros f l. unfold runPC. reflexivity. Qed.
Definition EUs_0_L : axst := Eval vm_compute in (leaf 0 (runPC 0 true)).
Definition EM_0_L : axst := Eval vm_compute in (leaf 1 (runPC 0 true)).
Definition EUs_0_M : axst := Eval vm_compute in (leaf 0 (runPC 0 false)).
Definition EM_0_M : axst := Eval vm_compute in (leaf 1 (runPC 0 false)).
Definition EUs_1_L : axst := Eval vm_compute in (leaf 0 (runPC 1 true)).
Definition EM_1_L : axst := Eval vm_compute in (leaf 1 (runPC 1 true)).
Definition EUs_1_M : axst := Eval vm_compute in (leaf 0 (runPC 1 false)).
Definition EM_1_M : axst := Eval vm_compute in (leaf 1 (runPC 1 false)).
Definition EUs_2_L : axst := Eval vm_compute in (leaf 0 (runPC 2 true)).
Definition EM_2_L : axst := Eval vm_compute in (leaf 1 (runPC 2 true)).
Definition EUs_2_M : axst := Eval vm_compute in (leaf 0 (runPC 2 false)).
Definition EM_2_M : axst := Eval vm_compute in (leaf 1 (runPC 2 false)).
Definition EUs (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Sb7Sb8X2x2S0S0SfLn;R1G0Vl;Sb9SbaX2x2S0G0Vl;SbbSbcX2x2Ln0;X0x2Ln;X0x2").
Definition EM (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S98S99X2x2S0S0SfLn;R1G0Vl;S9aS9bX2x2S0G0Vl;S9cS9dX2x2Ln0;X0x2Ln;X0x2").
Definition TsPC (f : nat) (l : bool) : list (axst * vmap) := ltac2:(tb__ "0|2|
S1S4SfS35A2M0S3SfS35Sb6Vf;Vl;A2S108S4dVl;A1A1M1A4S1G0S3SfS35S42Vf;Vl;A2G1A4S5G0A1A3A3").

Definition D_M : list sobj := ltac2:(tb__ "0|0|
S1S17S6aS3aS3cA2S5S17A1A3").
Definition EMxof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S5cS42Vf;Vl;A2S49A2").
Definition EMdof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S7bS42Vf;Vl;A2S49A2").
Definition EMx_0_L : axst := Eval vm_compute in (EMxof 0 true).
Definition EMd_0_L : axst := Eval vm_compute in (EMdof 0 true).
Definition EMx_0_M : axst := Eval vm_compute in (EMxof 0 false).
Definition EMd_0_M : axst := Eval vm_compute in (EMdof 0 false).
Definition EMx_1_L : axst := Eval vm_compute in (EMxof 1 true).
Definition EMd_1_L : axst := Eval vm_compute in (EMdof 1 true).
Definition EMx_1_M : axst := Eval vm_compute in (EMxof 1 false).
Definition EMd_1_M : axst := Eval vm_compute in (EMdof 1 false).
Definition EMx_2_L : axst := Eval vm_compute in (EMxof 2 true).
Definition EMd_2_L : axst := Eval vm_compute in (EMdof 2 true).
Definition EMx_2_M : axst := Eval vm_compute in (EMxof 2 false).
Definition EMd_2_M : axst := Eval vm_compute in (EMdof 2 false).
Definition EMx (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Sa4Sa5X2x2S0S0SfLn;R1G0Vl;Sa6Sa7X2x2S0G0Vl;Sa8Sa9X2x2Ln0;X0x2Ln;X0x2").
Definition EMd (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S9eS9fX2x2S0S0SfLn;R1G0Vl;Sa0Sa1X2x2S0G0Vl;Sa2Sa3X2x2Ln0;X0x2Ln;X0x2").

Definition AMof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S11aS63Vf;Vl;A2S19Z0A1A2").
Definition AM_0_L : axst := Eval vm_compute in (AMof 0 true).
Definition AM_0_M : axst := Eval vm_compute in (AMof 0 false).
Definition AM_1_L : axst := Eval vm_compute in (AMof 1 true).
Definition AM_1_M : axst := Eval vm_compute in (AMof 1 false).
Definition AM_2_L : axst := Eval vm_compute in (AMof 2 true).
Definition AM_2_M : axst := Eval vm_compute in (AMof 2 false).
Definition AM (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S7fS80X2x2S0S0SfLn;R1G0Vl;S81S82X2x2S0G0Vl;S83S84X2x2Ln0;X0x2Ln;X0x2").
Definition runPD (f : nat) (l : bool) : list leafA := ltac2:(tb__ "0|0|
SfaU384S5S14A1S40Vf;Vl;A2A3").
Lemma runPD_eq : ltac2:(tb__ "0|0|
S0S2S38S6S11A1SfaU384S5S14A1S40R2R1A2A3S59R2R1A2A3Fl;Ff;"). Proof. intros f l. unfold runPD. reflexivity. Qed.
Definition EU_0_L : axst := Eval vm_compute in (leaf 0 (runPD 0 true)).
Definition EU_0_M : axst := Eval vm_compute in (leaf 0 (runPD 0 false)).
Definition EU_1_L : axst := Eval vm_compute in (leaf 0 (runPD 1 true)).
Definition EU_1_M : axst := Eval vm_compute in (leaf 0 (runPD 1 false)).
Definition EU_2_L : axst := Eval vm_compute in (leaf 0 (runPD 2 true)).
Definition EU_2_M : axst := Eval vm_compute in (leaf 0 (runPD 2 false)).
Definition EU (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;SaaSabX2x2S0S0SfLn;R1G0Vl;SacSadX2x2S0G0Vl;SaeSafX2x2Ln0;X0x2Ln;X0x2").
Definition TsPD (f : nat) (l : bool) : list (axst * vmap) := ltac2:(tb__ "0|1|
S1S4SfS35A2M0S3SfS35S43Vf;Vl;A2S108S4dVl;A1A1A4S5G0A1A3").

Definition D_U (l : bool) : list sobj := ltac2:(tb__ "0|2|
S7S17S1S17S70S1S17S71S1S17S6fS1S17S6eS1S17S72S1S17S6cS1S17S6bS3aS3cA2S1S17S51S3aS19Z0A1M0A2S1S17S50G0A1S5S17A1M1A3A3A3A3A3A3A3A3A3S2S6S17A1Ll;Vl;G1S1S17S69G0A1S1S17S6dG1A3A3X2x2A3").
Definition EUxof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S5cS43Vf;Vl;A2S4aVl;A1A2").
Definition EUdof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S7bS43Vf;Vl;A2S4aVl;A1A2").
Definition EUx_0_L : axst := Eval vm_compute in (EUxof 0 true).
Definition EUd_0_L : axst := Eval vm_compute in (EUdof 0 true).
Definition EUx_0_M : axst := Eval vm_compute in (EUxof 0 false).
Definition EUd_0_M : axst := Eval vm_compute in (EUdof 0 false).
Definition EUx_1_L : axst := Eval vm_compute in (EUxof 1 true).
Definition EUd_1_L : axst := Eval vm_compute in (EUdof 1 true).
Definition EUx_1_M : axst := Eval vm_compute in (EUxof 1 false).
Definition EUd_1_M : axst := Eval vm_compute in (EUdof 1 false).
Definition EUx_2_L : axst := Eval vm_compute in (EUxof 2 true).
Definition EUd_2_L : axst := Eval vm_compute in (EUdof 2 true).
Definition EUx_2_M : axst := Eval vm_compute in (EUxof 2 false).
Definition EUd_2_M : axst := Eval vm_compute in (EUdof 2 false).
Definition EUx (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;SbdSbeX2x2S0S0SfLn;R1G0Vl;SbfSc0X2x2S0G0Vl;Sc1Sc2X2x2Ln0;X0x2Ln;X0x2").
Definition EUd (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Sb0Sb1X2x2S0S0SfLn;R1G0Vl;Sb2Sb3X2x2S0G0Vl;Sb4Sb5X2x2Ln0;X0x2Ln;X0x2").

Definition AUof (f : nat) (l : bool) : axst := ltac2:(tb__ "0|0|
S11aS65Vf;Vl;A2S19Z0A1A2").
Definition AU_0_L : axst := Eval vm_compute in (AUof 0 true).
Definition AU_0_M : axst := Eval vm_compute in (AUof 0 false).
Definition AU_1_L : axst := Eval vm_compute in (AUof 1 true).
Definition AU_1_M : axst := Eval vm_compute in (AUof 1 false).
Definition AU_2_L : axst := Eval vm_compute in (AUof 2 true).
Definition AU_2_M : axst := Eval vm_compute in (AUof 2 false).
Definition AU (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;S85S86X2x2S0S0SfLn;R1G0Vl;S87S88X2x2S0G0Vl;S89S8aX2x2Ln0;X0x2Ln;X0x2").
Definition runPE (f : nat) (l : bool) : list leafA := ltac2:(tb__ "0|0|
SfaU384S1S14S10aS5S14A1A3S41Vf;Vl;A2A3").
Lemma runPE_eq : ltac2:(tb__ "0|0|
S0S2S38S6S11A1SfaU384S1S14S10aS5S14A1A3S41R2R1A2A3S5aR2R1A2A3Fl;Ff;"). Proof. intros f l. unfold runPE. reflexivity. Qed.
Definition LR_0_L : axst := Eval vm_compute in (leaf 0 (runPE 0 true)).
Definition LR_0_M : axst := Eval vm_compute in (leaf 0 (runPE 0 false)).
Definition LR_1_L : axst := Eval vm_compute in (leaf 0 (runPE 1 true)).
Definition LR_1_M : axst := Eval vm_compute in (leaf 0 (runPE 1 false)).
Definition LR_2_L : axst := Eval vm_compute in (leaf 0 (runPE 2 true)).
Definition LR_2_M : axst := Eval vm_compute in (leaf 0 (runPE 2 false)).
Definition LR (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S0SfLf;Vf;S2SfLl;M0Vl;Sd0Sd1X2x2S0S0SfLn;R1G0Vl;Sd2Sd3X2x2S0G0Vl;Sd4Sd5X2x2Ln0;X0x2Ln;X0x2").
Definition TsPE (f : nat) (l : bool) : list (axst * vmap) := ltac2:(tb__ "0|1|
S1S4SfS35A2M0S3SfS35ScfVf;Vl;A2S108S4dVl;A1A1A4S5G0A1A3").

Ltac fam3 := let f := fresh "f" in intros f; destruct f as [|[|[|f]]].
Ltac fam6 := let f := fresh "f" in let l := fresh "l" in intros f l; destruct f as [|[|[|f]]]; destruct l.
Definition famok (f : nat) : bool := Nat.leb f 2.
Lemma chkPA : ltac2:(tb__ "0|0|
S0S38S2S36S1aS10S46R1A1A1A1S56R1A1S74R1A1A3S8A3Ff;"). Proof. fam3; vm_cast_no_check (eq_refl true). Qed.
Lemma chkPL : ltac2:(tb__ "0|0|
S0S38S2S36S1aS10S3eR1A1A1A1S5bR1A1S79R1A1A3S8A3Ff;"). Proof. fam3; vm_cast_no_check (eq_refl true). Qed.
Lemma chkPB : ltac2:(tb__ "0|0|
S0S2S38S2S36S1aS10S47R2R1A2A1A1S57R2R1A2S75R2R1A2A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.
Lemma chkPC : ltac2:(tb__ "0|0|
S0S2S38S2S36S1aS10S3dR2R1A2A1A1S58R2R1A2S76R2R1A2A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.
Lemma chkPD : ltac2:(tb__ "0|0|
S0S2S38S2S36S1aS10S40R2R1A2A1A1S59R2R1A2S77R2R1A2A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.
Lemma chkPE : ltac2:(tb__ "0|0|
S0S2S38S2S36S1aS10S41R2R1A2A1A1S5aR2R1A2S78R2R1A2A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.

Lemma EMx_eq : ltac2:(tb__ "0|1|
S0S2S38SbSfA1S107S42R2R1A2M0S1S105S106S5dG0S49A2A1S5S105A1A3A2ScSfS64R2R1A2A2A3Fl;Ff;"). Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.
Lemma EUx_eq : ltac2:(tb__ "0|1|
S0S2S38SbSfA1S107S43R2R1A2M0S1S105S106S5dG0S4aR1A1A2A1S5S105A1A3A2ScSfS66R2R1A2A2A3Fl;Ff;"). Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.
Lemma EMd_eq : ltac2:(tb__ "0|0|
S0S2S38SfS63R2R1A2S4eS64R2R1A2U1A2A3Fl;Ff;"). Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.
Lemma EUd_eq : ltac2:(tb__ "0|0|
S0S2S38SfS65R2R1A2S4eS66R2R1A2S2S0Ll;R1U9UbX2x2A2A3Fl;Ff;"). Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.

Lemma runs_shape : ltac2:(tb__ "0|7|
S0S2S38S4S4S4S4S4S4S4S0S0A2M0S0A2M1S0A2M2S0A2M3S0A2M4S0A2M5S0A2S3G5S0S3G4S0S3G3S0S3G2S0S3G1S0S3G0S0S3S0S0S9S11S56R2A1A2S9S11S5bR2A1A2A4S9S11S57R2R1A2A2A4S9S11S58R2R1A2A2A4S9S11S59R2R1A2A2A4S9S11S5aR2R1A2A2A4S53S42R2R1A2S49A2A4S53S43R2R1A2S4aR1A1A2A4S3G5S0S3G4S0S3G3S0S3G2S0S3G1S0S3G0S0S3S0S0U1M6U8A4G6A4U2A4G6A4G6A4G6A4S2S0Ll;R1U9UbX2x2A4A3Fl;Ff;").
Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.

Lemma He5 : ltac2:(tb__ "0|1|
S0S2S38SbS6S17A1M0A1S117S3bR2R1A2S102S48R2R1A2A3ScG0S4bR2R1A2A2A3Fl;Ff;").
Proof. fam6; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk5 : ltac2:(tb__ "0|0|
S0S2S38S2S119S3bR2R1A2S102S48R2R1A2S4bR2R1A2S114S11SfS13S103A4A5S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.

Lemma HT5 : ltac2:(tb__ "0|0|
S0S2S11SfeS11R1S103A3S38SfS118S48R4R3A2S102S13R2A1S3bR4R3A2S4bR4R3A2A5S4cR4R3A2A3F_;FP;Fl;Ff;").
Proof. intros f l P [<-|[]]. reflexivity. Qed.
Lemma T5f_eq : ltac2:(tb__ "0|0|
S0S2S38SfS116S4cR2R1A2S20S10S3bR2R1A2A1A1A2S3dR2R1A2A3Fl;Ff;"). Proof. fam6; match goal with |- _ = ?x => vm_cast_no_check (eq_refl x) end. Qed.
Lemma FBC5 : ltac2:(tb__ "0|1|
S0S2S38S2SffS18S2aS1aS10S3bR2R1A2A1M0A1A1S20G0A1A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.
Lemma FBT5 : ltac2:(tb__ "0|0|
S0S2S38S2SffS18S2aS1aS10S4cR2R1A2A1A1A1S20S10S3bR2R1A2A1A1A3S8A3Fl;Ff;"). Proof. fam6; vm_cast_no_check (eq_refl true). Qed.
Lemma NXC5 : ltac2:(tb__ "0|0|
S0S2S100SfbS1aS10S3bR2R1A2A1A1A2Fl;Ff;"). Proof. fam6; apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nxS : ltac2:(tb__ "0|6|
S39S0S39S38S2S1eS10S46R1A1A1M0A1SaA3S100SfbS1aG0A1A2A2Ff;S39S0S39S38S2S1eS10S3eR1A1A1M1A1SaA3S100SfbS1aG1A1A2A2Ff;S39S0S2S39S38S2S1eS10S47R2R1A2A1M2A1SaA3S100SfbS1aG2A1A2A2Fl;Ff;S39S0S2S39S38S2S1eS10S3dR2R1A2A1M3A1SaA3S100SfbS1aG3A1A2A2Fl;Ff;S39S0S2S39S38S2S1eS10S40R2R1A2A1M4A1SaA3S100SfbS1aG4A1A2A2Fl;Ff;S0S2S39S38S2S1eS10S41R2R1A2A1M5A1SaA3S100SfbS1aG5A1A2A2Fl;Ff;A2A2A2A2A2").
Proof.
  split; [fam3; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])|].
  split; [fam3; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])|].
  split; [fam6; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])|].
  split; [fam6; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])|].
  split; [fam6; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])|].
  fam6; (split; [reflexivity | apply Pos.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]).
Qed.

Section TR.
Context {Q : assn} (X : trk Q).
Theorem seg_PA : ltac2:(tb__ "0|0|
S0Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S74R8A1A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S46R6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Ff;").
Proof. intros f J rho tp HJ HC. exact (tr_piece X 300%nat _ (S0 f) (runPA f) (TsPA f) (runPA_eq f) (chkPA f) (proj1 (proj1 nxS f)) (proj2 (proj1 nxS f)) J rho tp HJ HC). Qed.
Theorem seg_PL : ltac2:(tb__ "0|0|
S0Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S79R8A1A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S3eR6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Ff;").
Proof. intros f J rho tp HJ HC. exact (tr_piece X 100%nat _ (SC f) (runPL f) (TsPL f) (runPL_eq f) (chkPL f) (proj1 (proj1 (proj2 nxS) f)) (proj2 (proj1 (proj2 nxS) f)) J rho tp HJ HC). Qed.
Theorem seg_PB : ltac2:(tb__ "0|0|
S0S2Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S75R9R8A2A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S47R7R6A2R4R3A5A3F_;F_;Ftp;Frho;FJ;Fl;Ff;").
Proof. intros f l J rho tp HJ HC. exact (tr_piece X 900%nat _ (SX f l) (runPB f l) (TsPB f l) (runPB_eq f l) (chkPB f l) (proj1 (proj1 (proj2 (proj2 nxS)) f l)) (proj2 (proj1 (proj2 (proj2 nxS)) f l)) J rho tp HJ HC). Qed.
Theorem seg_PC : ltac2:(tb__ "0|0|
S0S2Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S76R9R8A2A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S3dR7R6A2R4R3A5A3F_;F_;Ftp;Frho;FJ;Fl;Ff;").
Proof. intros f l J rho tp HJ HC. exact (tr_piece X 900%nat _ (T5f f l) (runPC f l) (TsPC f l) (runPC_eq f l) (chkPC f l) (proj1 (proj1 (proj2 (proj2 (proj2 nxS))) f l)) (proj2 (proj1 (proj2 (proj2 (proj2 nxS))) f l)) J rho tp HJ HC). Qed.
Theorem seg_PD : ltac2:(tb__ "0|0|
S0S2Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S77R9R8A2A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S40R7R6A2R4R3A5A3F_;F_;Ftp;Frho;FJ;Fl;Ff;").
Proof. intros f l J rho tp HJ HC. exact (tr_piece X 900%nat _ (AM f l) (runPD f l) (TsPD f l) (runPD_eq f l) (chkPD f l) (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 nxS)))) f l)) (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 nxS)))) f l)) J rho tp HJ HC). Qed.
Theorem seg_PE : ltac2:(tb__ "0|0|
S0S2Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3SfS35S1cSfeS4SfS35A2S3SfS35R3R2A4S78R9R8A2A3S37R3R7R2A3Sf7VQ;VX;Sf3Sf6R9R5R3R7A5A3F_;F_;Frho';FM;FT;Sf7VQ;VX;Sf3Sf6R5S41R7R6A2R4R3A5A3F_;F_;Ftp;Frho;FJ;Fl;Ff;").
Proof. intros f l J rho tp HJ HC. exact (tr_piece X 900%nat _ (AU f l) (runPE f l) (TsPE f l) (runPE_eq f l) (chkPE f l) (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 nxS)))) f l)) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 nxS)))) f l)) J rho tp HJ HC). Qed.

Theorem qs_memset : ltac2:(tb__ "0|1|
S0S2Sf4S1cS6S101Q40A1A1Sf8VQ;VX;R3A3S1cS2cS1aS10S3bR7R6A2M0A1A1R4R1A3Sf7VQ;VX;Sf3Sf6R6S3dR8R7A2R2R4A5A3F_;Frho';Sf7VQ;VX;Sf3Sf6R5G0R4R3A5A3F_;F_;Ftp;FrhoE;FJ;Fl;Ff;").
Proof.
  intros f l J rhoE tp HJ HC.
  apply (tr_call X (C5 f l) Pre_memsetA Posts_memsetA (s5 f l) (R5 f l) (T5of f l)
           (fun ok Jx rho tp0 Hok Hst => memset_sumA ok Jx rho tp0 Hok Hst) (fun Jx rho tp0 Hst => memset_sumA_ex Jx rho tp0 Hst)
           (He5 f l) (Hchk5 f l) (HT5 f l) (FBC5 f l) (FBT5 f l) (NXC5 f l) J rhoE tp HJ).
  intros rho' Hag. rewrite (T5f_eq f l). exact (HC rho' Hag).
Qed.
End TR.

End SegQS_states.

(* [comment removed for export] *)
Module SpineCallocS8.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "nil"; "true"; "cons"; "list"; "pair"; "prod"; "nat"; "Some"; "option"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SVar"; "ss_facts"; "valuation"; "ss_next"; "SPBranch"; "SLit"; "rw"; "swf"; "SPNot"; "sobj"; "SAlu"; "eval"; "SPUle"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "V_CLS"; "E7c1"; "E7c2"; "F_gen"; "C7p"; "E7q1"; "E7q2"; "E7p"; "V_ND"; "n8e"; "upd"; "C8"; "C8p"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "BP"; "C7"; "LPe"; "ube"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "JGb"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "add"; "mul"; "le"; "lt"; "of_nat"; "sub"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "ALU_ADD"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "tab_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8.S8.B11S"; "E7c1'"; "E7c2'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8.S8.B12S"; "E7q1'"; "E7q2'"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "needed8"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8"; "a0e7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4"; "pvals_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition a0e7 : sv := ltac2:(tb__ "0|0|
S1eS59S1eS5aS1eS59S3bS30A3S19Z3A1A3S40A3").

Section PSVals7.
Variable rho : valuation.
Variables SB c x rzv sz n : Z.
Hypothesis PV : ltac2:(tb__ "0|0|
S6bVrho;VSB;Vc;Vx;Vrzv;Vsz;Vn;A7").
Let ab : Z := ltac2:(tb__ "0|0|
S45S45VSB;S46Vc;S4bZ2Z20A2A2A2S46Z10Vx;A2A2").
Ltac pv := pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).

Lemma pv_a0e7 : ltac2:(tb__ "0|0|
S0S4cQ40A1S1fVrho;S6aA2S1fVrho;S38A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ub rho _ _ _ _ _ _ PV) as EUB. cbn zeta in EUB. fold ab in EUB.
  pose proof (pv_bp rho _ _ _ _ _ _ PV) as EBP. cbn zeta in EBP. fold ab in EBP.
  apply bv_eq. rewrite EBP. unfold a0e7, shb. cbn [eval]. fold ube. fold n8e.
  assert (EN8 : bv_unsigned (eval rho n8e) = n - n mod 8).
  { unfold n8e. cbn [eval]. rewrite and_val, E12, !u64_lit by (unfold M48; lia). apply land_M48. lia. }
  rewrite add_val, srl_val, add_val, EUB, EN8, !u64_lit by (unfold SHADOW_OFF; lia). change (3 mod 64) with 3.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  assert (B1 : 17594333495296 <= ab + rzv /\ ab + rzv + n <= 140737479966720) by (unfold ab; lia).
  rewrite (Z.mod_small (ab + rzv + _)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Sh_small rho _ _ _ _ _ _ PV (ab + rzv + (n - n mod 8)) ltac:(lia)) as (_ & E & _). rewrite E.
  unfold Sh. pose proof (Z.div_mod rzv 16 ltac:(lia)). pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)).
  replace (ab + rzv + (n - n mod 8)) with (ab + rzv + (n / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Lemma pv_lp1 : ltac2:(tb__ "0|0|
S2S0S22S44Vn;Z8A2Z0A3A1S0S22S4dQ40S1fVrho;S3aA2A2Z1A3F_;").
Proof. intros Hn. rewrite (pv_lp rho _ _ _ _ _ _ PV). destruct (Z.eq_dec (n mod 8) 0); [contradiction | reflexivity]. Qed.
End PSVals7.

Section S8.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S55VAInv;VW;Vst;VA;VKc;S14PcA1A6").

Lemma class_restate_gen : ltac2:(tb__ "0|7|
S4S21S13S22SeS56S53S16SbS4cQ40M0A1A1S42S16S0S7S5dP9dM1R9A2S9A3S0S7S5eG1RaS5cR9R8A5S9A3S0S7S1bRcA1S9A3S0S10SdSbSdS13S13A2M2A1M3SbS12A1M4A2M5A1S52S3ReA1RdA2SfG5ScG3G4SaG2ScS13S13RcS14S27A1A4S8G2A1A3S8S12A1A4A2A3S0S23S17ReA1S17S3RfA1A1A3S68S4dG0S1aR9PcA2A2A1S22S1S1S47ReR1A2S48R1S45ReS46Z8M6S49RdA1A2A2A2A2S0S22S44S4aR1ReA2G6A2Z0A3A2Tnd;S24Vsegs;S3cVW;Vst;RcRbRaA5R11R7R9R8A6S24Vsegs;S3cVW;Vst;RdRcRbA5S6R12R11A2R8RaR9A6F_;F_;F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;Fcnt;Flo;Fcreg;FES;FE;").
Proof.
  intros E ES creg lo cnt A Kc rho tp w rhoE OV TAB WS DS NX [Hr Hm] Hw.
  destruct w as [tr [ms md]]. pose proof (proj2 Hw) as [Hag HJ]. destruct Hag as (Hagw & _ & _).
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 (bv_unsigned (rw rho 12%positive)))). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of (bv_unsigned (rw rho 12%positive)))). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  eapply SPA_restate; [exact WS | exact DS | exact NX | | constructor | exact Hw].
  unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_CLS. cbn [eval]. rewrite E158.
  exact (tab_ok_sound 157 _ ClassID lo cnt rhoE _ TAB OV E157 Hr Hm).
Qed.

Lemma needed_range : ltac2:(tb__ "0|6|
S56S53S16S16SbS4cQ40M0A1A1S42S4S7S24Vsegs;S3cVW;Vst;R8R7R6A5R2R5R4R3A6S3eS12S2aS15S3R3A1A1A3S3dS12S7S12Lb;R3S18S57S19Z200A1S14S2fA1A3M1S1cG1A1X7x2S15S3R4A1A1A3S68S4dG0S1aR9PcA2A2A1S22S7OLb;R5S1S1S47Z208M2R1A2S48R1S45G2S46Z8M3S49S63S64S4eS4fS50S4eS51A1A1A1A1A1A1A1A2A2A2A2S0S22S44S4aR1G2A2G3A2Z0M4A3A2S1S1S47Z18M5R1A2S48R1S45G5S46G3S49U3eA1A2A2A2A2S0S22S44S4aR1G5A2G3A2G4A3A2X7x2Tnd;F_;F_;F_;Fb;FE;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w E b Hw HG HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. destruct Hag as (Hagw & _ & _). destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in *. cbn zeta.
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (NB0 : 0 <= needed8 nv < 2 ^ 62).
  { unfold needed8, round_up. pose proof (rz_bound nv). pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.div_pos (Z.max nv 8 + 8 - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (G1 : holds rhoE (SPUle (SLit 24) (SVar V_ND))) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  assert (G2 : holds rhoE (SPUle (SVar V_ND) (SLit 65536))) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  assert (G3 : holds rhoE (SPAlign V_ND 3)) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  cbn [holds eval] in G1, G2, G3. unfold V_ND in G1, G2, G3. rewrite E157 in G1, G2, G3. rewrite !u64_lit in G1, G2 by lia.
  destruct G3 as [_ G3]. rewrite u64_lit in G3 by lia. change (2 ^ 3) with 8 in G3.
  pose proof (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw HF) as F1.
  destruct b; cbn [holds eval] in F1; unfold V_ND in F1; rewrite E157 in F1; rewrite bt_ltu_lit in F1 by lia.
  - apply Z.ltb_lt in F1. split; [cbn; lia|]. replace (needed8 nv - 520) with (needed8 nv + (- 65) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
  - assert (needed8 nv <= 512) by (destruct (Z.ltb_spec 512 (needed8 nv)); [exfalso; apply F1; reflexivity | lia]).
    split; [cbn; lia|]. replace (needed8 nv - 24) with (needed8 nv + (- 3) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
Qed.

Section B11S.
Hypothesis Cert7 : ltac2:(tb__ "0|1|
S0S7S65S66Ufa0SaS22Z3c728SaS22Z3c870S8S22A1A3A3S3fSaS4S39VW;Vst;Vtmax;A3S8S4A1M0A3SaS4S28VW;Vst;Vtmax;A3SaS4S29VW;Vst;Vtmax;A3SaS4S2eVW;Vst;Vtmax;A3G0A3A3A3A6S9A3").
Definition E7c1' : axst := ltac2:(tb__ "0|1|
S31VW;Vst;Vtmax;S28VW;Vst;Vtmax;A3Z3c870SaSdSeS13A2M0ScSeS13UbS14S27A1A4S8G0A1A3S8S1dA1S11S8S12A1A9").
Definition E7c2' : axst := ltac2:(tb__ "0|1|
S31VW;Vst;Vtmax;S29VW;Vst;Vtmax;A3Z3c870SaSdSeS13A2M0ScSeS13UbS14S27A1A4S8G0A1A3S8S1dA1S11S8S12A1A9").
Hypothesis OV7a : ltac2:(tb__ "0|0|
S0S7S5dP9dS34VW;Vst;Vtmax;A3A2S9A3").
Hypothesis OV7b : ltac2:(tb__ "0|0|
S0S7S5dP9dS35VW;Vst;Vtmax;A3A2S9A3").
Hypothesis TAB7a : ltac2:(tb__ "0|0|
S0S7S5eP9dS34VW;Vst;Vtmax;A3S5cZ208S63S64S4eS4fS50S4eS51A1A1A1A1A1A1A5S9A3").
Hypothesis TAB7b : ltac2:(tb__ "0|0|
S0S7S5eP9dS35VW;Vst;Vtmax;A3S5cZ18U3eA5S9A3").
Hypothesis W7a : ltac2:(tb__ "0|0|
S0S7S1bS3S5fA1A1S9A3").
Hypothesis W7b : ltac2:(tb__ "0|0|
S0S7S1bS3S60A1A1S9A3").
Hypothesis D7a : ltac2:(tb__ "0|4|
S0S10SdSbSdS13S13A2M0A1M1SbS12A1M2A2M3A1S52S3S28VW;Vst;Vtmax;A3A1S3S5fA1A2SfG3ScG1G2SaG0ScS13S13S34VW;Vst;Vtmax;A3S14S27A1A4S8G0A1A3S8S12A1A4A2A3").
Hypothesis D7b : ltac2:(tb__ "0|4|
S0S10SdSbSdS13S13A2M0A1M1SbS12A1M2A2M3A1S52S3S29VW;Vst;Vtmax;A3A1S3S60A1A2SfG3ScG1G2SaG0ScS13S13S35VW;Vst;Vtmax;A3S14S27A1A4S8G0A1A3S8S12A1A4A2A3").
Hypothesis NX7a : ltac2:(tb__ "0|0|
S0S23S17S3S5fA1A1S17S3S28VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7b : ltac2:(tb__ "0|0|
S0S23S17S3S60A1A1S17S3S29VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7a : ltac2:(tb__ "0|0|
S3eS12S2aS15S3S28VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7b : ltac2:(tb__ "0|0|
S3eS12S2aS15S3S29VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7a : ltac2:(tb__ "0|0|
S3dS12S18S57S19Z200A1S14S2fA1A3S15S3S28VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7b : ltac2:(tb__ "0|0|
S3dS12S1cS18S57S19Z200A1S14S2fA1A3A1S15S3S29VW;Vst;Vtmax;A3A1A1A3").
Variables s8a s8b : wsub.
Hypothesis ENT8a : ltac2:(tb__ "0|0|
S0S7S5S5fS32VW;Vst;Vtmax;A3Vs8a;A3S9A3").
Hypothesis ENT8b : ltac2:(tb__ "0|0|
S0S7S5S60S32VW;Vst;Vtmax;A3Vs8b;A3S9A3").
Hypothesis SID8a : ltac2:(tb__ "0|0|
S0S7S5bVs8a;S3fA2S9A3").
Hypothesis SID8b : ltac2:(tb__ "0|0|
S0S7S5bVs8b;S3fA2S9A3").

Hypothesis G7p : ltac2:(tb__ "0|0|
S3eS12S2aS15S3S2eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7p : ltac2:(tb__ "0|0|
S3dS12S1cS18S58S14PcA1S30A3A1S15S3S2eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W7p : ltac2:(tb__ "0|0|
S0S7S1bS3S2bVW;Vst;Vtmax;A3A1A1S9A3").
Hypothesis D7p : ltac2:(tb__ "0|4|
S0S10SdSbSdS13S13A2M0A1M1SbS12A1M2A2M3A1S52S3S2eVW;Vst;Vtmax;A3A1S3S2bVW;Vst;Vtmax;A3A1A2SfG3ScG1G2SaG0ScS13S13S6aS38A4S8G0A1A3SaS12S20S19Z1A1S3aA2S8S12A1A3A4A2A3").
Hypothesis NX7p : ltac2:(tb__ "0|0|
S0S23S17S3S2bVW;Vst;Vtmax;A3A1A1S17S3S2eVW;Vst;Vtmax;A3A1A1A3").

Hypothesis F7an : ltac2:(tb__ "0|0|
S3dS12S18S58S14PcA1S30A3S15S3S28VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7bn : ltac2:(tb__ "0|0|
S3dS12S18S58S14PcA1S30A3S15S3S29VW;Vst;Vtmax;A3A1A1A3").

Lemma nmod8_of_fact : ltac2:(tb__ "0|4|
S56S53S16S16SbS4cQ40M0A1A1S42S4S7S24Vsegs;S3cVW;Vst;R8R7R6A5R2R5R4R3A6S3eS12S2aS15S3R3A1A1A3S3dS12S7S12Lb;R3S18S58S14PcM1A1S30A3M2S1cG2A1X7x2S15S3R4A1A1A3S7OLb;R4S0S22S44S4dG0S1aR9G1A2A2Z8A2Z0A3M3S2G3A1X7x2F_;F_;F_;Fb;FE;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w E b Hw HG HF. destruct w as [tr [ms md]].
  pose proof (JGb_rigid nW st A Kc rho rhoE tp tr md (proj2 Hw)) as (E12 & _).
  destruct (JGb_model nW st A Kc rho rhoE tp tr md (proj2 Hw)) as [_ HN]. cbn zeta in HN.
  pose proof (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw HF) as F.
  assert (EV : bv_unsigned (eval rhoE n8e) = bv_unsigned (rw rho 12%positive) - bv_unsigned (rw rho 12%positive) mod 8).
  { unfold n8e. cbn [eval]. rewrite and_val, E12, u64_lit by (unfold M48; lia). apply land_M48. pose proof (urange (rw rho 12%positive)). lia. }
  destruct b; cbn [holds eval] in F; fold n8e in F; cbn [branch_taken] in F; unfold bv_eqb in F; rewrite E12, EV in F.
  - apply Z.eqb_eq in F. lia.
  - intros E0. apply F. apply Z.eqb_eq. lia.
Qed.

Theorem spine_s7 : ltac2:(tb__ "0|5|
S42OF_;S56S53S16SbS4cQ40M0A1A1S43S67VW;Vst;A2S54R5A1S26Vsegs;R8S25R6A1A3S47Z1S69R8S4dG0S1aR6PcM1A2A2A2A2S0S22S44S4dG0S1aR7G1A2A2Z8M2A2Z0M3A3S16S41Vsegs;RcS24Vsegs;S3cVW;Vst;RbRaR9A5S32VW;Vst;Vtmax;A3R1R8A5R7A4FrhoX;F_;S2S0S22S44S4dG0S1aR8G1A2A2G2A2G3A3A1S16S41Vsegs;RdS24Vsegs;S3cVW;Vst;RcRbRaA5M4S2bVW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;S16S41Vsegs;RdS24Vsegs;G4S39VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt HC8 HC7p rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c728; 0x3c870] GW [C7 W st tmax] [E7c1 W st tmax; E7c2 W st tmax; E7p W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert7.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[<-|[]]]].
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ true Hw G7a F7an)|]. intros Hm0.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8a))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7c1' (C8 W st tmax) s8a rhoX tp w ENT8a SID8a); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c1', upd. lazy zeta.
      apply (class_restate_gen (E7c1 W st tmax) _ (creg7a W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7a TAB7a W7a D7a NX7a); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ true Hw G7a F7a).
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ true Hw G7b F7bn)|]. intros Hm0.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8b))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7c2' (C8 W st tmax) s8b rhoX tp w ENT8b SID8b); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c2', upd. lazy zeta.
      apply (class_restate_gen (E7c2 W st tmax) _ (creg7b W st tmax) 24 62%nat A Kc rho tp w rhoX OV7b TAB7b W7b D7b NX7b); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ false Hw G7b F7b).
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 <> 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ false Hw G7p F7p)|]. intros Hm8.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7p Hm8 rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G7p Hcnt) as PV. cbn zeta in PV.
      destruct w as [tr [ms md]].
      unfold C7p, upd. lazy zeta. eapply SPA_restate; [exact W7p | exact D7p | exact NX7p | | | exact Hw].
      * unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_a0e7 rhoX _ _ _ _ _ _ PV).
      * apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. fold LPe. rewrite (pv_lp1 rhoX _ _ _ _ _ _ PV Hm8). rewrite u64_lit by lia. lia.
  - left. reflexivity.
Qed.
End B11S.

Section B12S.
Hypothesis Cert7p : ltac2:(tb__ "0|1|
S0S7S65S66Ufa0SaS22Z3c870S8S22A1A3S3fSaS4S2bVW;Vst;Vtmax;A3S8S4A1M0A3SaS4S2cVW;Vst;Vtmax;A3SaS4S2dVW;Vst;Vtmax;A3G0A3A3A6S9A3").
Definition E7q1' : axst := ltac2:(tb__ "0|1|
S31VW;Vst;Vtmax;S2cVW;Vst;Vtmax;A3Z3c870SaSdSeS13A2M0ScSeS13UbS14S27A1A4S8G0A1A3S8S1dA1S11S8S12A1A9").
Definition E7q2' : axst := ltac2:(tb__ "0|1|
S31VW;Vst;Vtmax;S2dVW;Vst;Vtmax;A3Z3c870SaSdSeS13A2M0ScSeS13UbS14S27A1A4S8G0A1A3S8S1dA1S11S8S12A1A9").
Hypothesis OV7c : ltac2:(tb__ "0|0|
S0S7S5dP9dS36VW;Vst;Vtmax;A3A2S9A3").
Hypothesis OV7d : ltac2:(tb__ "0|0|
S0S7S5dP9dS37VW;Vst;Vtmax;A3A2S9A3").
Hypothesis TAB7c : ltac2:(tb__ "0|0|
S0S7S5eP9dS36VW;Vst;Vtmax;A3S5cZ208S63S64S4eS4fS50S4eS51A1A1A1A1A1A1A5S9A3").
Hypothesis TAB7d : ltac2:(tb__ "0|0|
S0S7S5eP9dS37VW;Vst;Vtmax;A3S5cZ18U3eA5S9A3").
Hypothesis W7c : ltac2:(tb__ "0|0|
S0S7S1bS3S61A1A1S9A3").
Hypothesis W7d : ltac2:(tb__ "0|0|
S0S7S1bS3S62A1A1S9A3").
Hypothesis D7c : ltac2:(tb__ "0|4|
S0S10SdSbSdS13S13A2M0A1M1SbS12A1M2A2M3A1S52S3S2cVW;Vst;Vtmax;A3A1S3S61A1A2SfG3ScG1G2SaG0ScS13S13S36VW;Vst;Vtmax;A3S14S27A1A4S8G0A1A3S8S12A1A4A2A3").
Hypothesis D7d : ltac2:(tb__ "0|4|
S0S10SdSbSdS13S13A2M0A1M1SbS12A1M2A2M3A1S52S3S2dVW;Vst;Vtmax;A3A1S3S62A1A2SfG3ScG1G2SaG0ScS13S13S37VW;Vst;Vtmax;A3S14S27A1A4S8G0A1A3S8S12A1A4A2A3").
Hypothesis NX7c : ltac2:(tb__ "0|0|
S0S23S17S3S61A1A1S17S3S2cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7d : ltac2:(tb__ "0|0|
S0S23S17S3S62A1A1S17S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7c : ltac2:(tb__ "0|0|
S3eS12S2aS15S3S2cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7d : ltac2:(tb__ "0|0|
S3eS12S2aS15S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7c : ltac2:(tb__ "0|0|
S3dS12S18S57S19Z200A1S14S2fA1A3S15S3S2cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7d : ltac2:(tb__ "0|0|
S3dS12S1cS18S57S19Z200A1S14S2fA1A3A1S15S3S2dVW;Vst;Vtmax;A3A1A1A3").
Variables s8c s8d : wsub.
Hypothesis ENT8c : ltac2:(tb__ "0|0|
S0S7S5S61S33VW;Vst;Vtmax;A3Vs8c;A3S9A3").
Hypothesis ENT8d : ltac2:(tb__ "0|0|
S0S7S5S62S33VW;Vst;Vtmax;A3Vs8d;A3S9A3").
Hypothesis SID8c : ltac2:(tb__ "0|0|
S0S7S5bVs8c;S3fA2S9A3").
Hypothesis SID8d : ltac2:(tb__ "0|0|
S0S7S5bVs8d;S3fA2S9A3").

Theorem spine_s7p : ltac2:(tb__ "0|0|
S42OF_;S56S53S16SbS4cQ40A1A1S43S67VW;Vst;A2S54R5A1S26Vsegs;R8S25R6A1A3S16S41Vsegs;RaS24Vsegs;S3cVW;Vst;R9R8R7A5S33VW;Vst;Vtmax;A3R1R6A5R5A4FrhoX;S16S41Vsegs;RbS24Vsegs;S3cVW;Vst;RaR9R8A5S2bVW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC8 rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c870] GW [C7p W st tmax] [E7q1 W st tmax; E7q2 W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert7p.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8c))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7q1' (C8p W st tmax) s8c rhoX tp w ENT8c SID8c); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q1', upd. lazy zeta.
      apply (class_restate_gen (E7q1 W st tmax) _ (creg7c W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7c TAB7c W7c D7c NX7c); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ true Hw G7c F7c).
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8d))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7q2' (C8p W st tmax) s8d rhoX tp w ENT8d SID8d); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q2', upd. lazy zeta.
      apply (class_restate_gen (E7q2 W st tmax) _ (creg7d W st tmax) 24 62%nat A Kc rho tp w rhoX OV7d TAB7d W7d D7d NX7d); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ false Hw G7d F7d).
  - left. reflexivity.
Qed.
End B12S.

Section B13C.

Variables (CC8 CC9 EE8n : axst).
Hypothesis Cert8 : ltac2:(tb__ "0|1|
S0S7S65S66Ufa0SaS22Zde378SaS22Z3c8c0S8S22A1A3A3S3fSaS4VCC8;S8S4A1M0A3SaS4VEE8n;G0A3A6S9A3").
Variable s9e : wsub.
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S0S7S5VEE8n;VCC9;Vs9e;A3S9A3").
Hypothesis SID9 : ltac2:(tb__ "0|0|
S0S7S5bVs9e;S3fA2S9A3").

Theorem spine_s8c : ltac2:(tb__ "0|2|
S42OF_;S56S53S16SbS4cQ40A1A1M0S43S67VW;Vst;A2S54R5A1S26Vsegs;R8S25R6A1A3S16G0S41Vsegs;RbS24Vsegs;S3cVW;Vst;RaR9R8A5M1VCC9;R2R1A5R6A4FtpX;FrhoX;S16S41Vsegs;RbS24Vsegs;G1VCC8;R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC9 rhoE.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  apply (cfg_soundA segs 4000%nat [0xde378; 0x3c8c0] GW [CC8] [EE8n] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - exact HST.
  - exact Cert8.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC9 (rho_sub rhoX s9e) tp)].
    exact (SPA_entails0 segs (JGb W st A Kc rho) GW EE8n CC9 s9e rhoX tp w ENT9 SID9 HST Hw).
  - left. reflexivity.
Qed.
End B13C.
End S8.
End SpineCallocS8.

(* [comment removed for export] *)
Module SpineCallocR3.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "rw"; "SLit"; "SVar"; "SAlu"; "rm"; "cell"; "ss_objs"; "sprop"; "ss_facts"; "SPBranch"; "eval"; "mkCell"; "obj_range"; "ss_lenient"; "ss_next"; "SExt"; "SPNot"; "ext_low"; "smatch"; "sstate"; "swf"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "sub"; "to_nat"; "of_nat"; "pow"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "bool"; "true"; "pair"; "prod"; "false"; "nat"; "option"; "app"; "Some"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "entailsA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "PV4"; "PV6"; "PV7"; "keepn"; "GR"; "O_cell"; "PNX"; "O_pcm"; "O_ri"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3.POP"; "JRpop"; "phK"; "O_dstc"; "O_srcc"; "e_end"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "FAb"; "PCE"; "ph_fill"; "frozen"; "ghosts"; "mkPh"; "ph_cnt"; "ph_f"; "ph_pop"; "ph_ri"; "ph_u"; "phase"; "rmlink"; "entryR"; "gh_new"; "gh_nf"; "rlink"; "zoneR"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "map"; "skipn"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "wsub_id_below"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "view"; "acell"; "c_addr"; "c_w"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "pc_base"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_thread"; "cs_cache"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refill_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cst_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sext32_small : ltac2:(tb__ "0|2|
S0S3S1fZ0R1A2S20R1S25Z2Z1fA2A2A2S2S35Q40M0A1S1aS2aQ20S36G0R2A2M1A3G1A3F_;Fz;").
Proof.
  intros z Hz. unfold ext_low. apply bv_eq.
  assert (E : bv_unsigned (bv_extract 0 32 (Z_to_bv 64 z)) = z).
  { rewrite bv_extract_unsigned. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.shiftr_0_r.
    change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). rewrite (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_small. lia. }
  rewrite sext64_32_small by (rewrite E; lia). rewrite E. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). symmetry. apply Z.mod_small. lia.
Qed.

Lemma view_absorb_out : ltac2:(tb__ "0|1|
S7S27S6A1S6fS0S6S68S6R1R4A3S4S3S1fS32S0S0S15R6R2A2M0A3R3A2S20R3S33S0S0G0A3A2A2A1F_;Fo;S2S2fS35Q8A1A1S74S34SdS6dR5R4R3A3A1R2A3S74S34SdR5A1R2A3A3F_;Fz;Fms;FR;Frho;").
Proof.
  intros rho R ms z Hout. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  unfold rd_of. rewrite rm_absorb_out; [reflexivity|].
  intros (o & Ho & Hr). apply (Hout o Ho). rewrite u64_lit in Hr by lia. exact Hr.
Qed.

Lemma rmlink_absorb : ltac2:(tb__ "0|1|
S35Q40A1S2fS35Q8A1A1F_;S7S27S6A1S6fS5eR4SdR3A1A2S6S68S6R1R4A3S5S1fS33S0S0S15R6R2A2M0A3S83A2S1fS82S32S0S0G0A3A2A2F_;Fo;S5eR6SdS6dR5R4R3A3A1A2F_;F_;Fms;FR;Frho;Ff0;").
Proof.
  intros f0 rho R ms H HR a Ha. rewrite rm_absorb_out; [exact (H a Ha)|].
  intros (o & Ho & Hr). rewrite u64_lit in Hr by (unfold IMG_LO, IMG_HI in Ha; lia). destruct (HR o Ho); lia.
Qed.

Lemma cell_ok_agree_range : ltac2:(tb__ "0|1|
S72S72S75S0S3S1fS76R2A1M0R1A2S20R1S1eG0S24S77R2A1A1A2A2A2S2S2fS35Q8A1A1R4R2A1R5R2A1A3F_;Fz;S73R4R2A2S73R4R3A2F_;F_;Fcc;Fm';Fm;").
Proof. intros m m' cc H Hc j Hj. rewrite H by lia. exact (Hc j Hj). Qed.

Lemma ph_eta : ltac2:(tb__ "0|0|
S5dS2S5dR1S57S5cR1A1S59R1A1S54R1A1S5aR1A1S58R1A1S5bR1A1A6A3Fp;").
Proof. intros p. destruct p. reflexivity. Qed.

Lemma nth_skipn_Z : ltac2:(tb__ "0|0|
S27S0A1S2eS2eS0S2S0S64S0R2S67S0R3R4A3R1A4S64S0S7fR3R2A2R4R1A4A3Fd;Fi;Fn;Fl;").
Proof. intros l n. revert l. induction n as [|n IH]; intros l i d; [reflexivity|]. destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn Nat.add nth]. apply IH. Qed.

Section POP.

Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S5fVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let k : Z := kchunks c.

Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S3S2S0S5aVph;A1Z0A3S3S2S29S58Vph;A1S2dA3S2S29S5bVph;A1S2dA3A2A2").
Definition phK (i : Z) : phase := ltac2:(tb__ "0|0|
S57S5cVph;A1S59Vph;A1S54Vph;A1Vi;S2dS2dA6").
Variable faP : list Z.
Let nfP : Z := Z.of_nat (length faP).
Hypothesis HSRC : ltac2:(tb__ "0|1|
S0S72S3S1fZ0M0R2A2S1fR2Vk;A2A2S62VA;Vrb;S4aR3A1S74S34SdVrb;A1A2R2A5S0S3S1fG0R1A2S20R1VnfP;A2A2S73R5S78S1eS52VA;Vrb;A2S21Z4R2A2A2U4S64S0S23R2A1VfaP;G0A4A3A2F_;Fidx;F_;F_;Fm;Fi;").
Hypothesis HKF : k <= nfP.
Hypothesis HNFP : 4 * nfP <= 536870912.
Hypothesis HFILLR : ltac2:(tb__ "0|4|
S20Z0M0S54Vph;A1M1A2S3S1fG0S61VA;Vrb;A2M2A2S3S2S0S1eG2S60VA;Vrb;A2M3A2VnfP;A3S1fG1G3A2A2A2F_;").
Hypothesis HIDS : ltac2:(tb__ "0|0|
S0S68S0R1VfaP;A3S3S1fZ0R2A2S20R2S25Z2Z1cA2A2A2F_;Fx;").
Hypothesis HCACHE : ltac2:(tb__ "0|0|
S2S27S0A1S87S88Vc;S8cVA;Vnv;A2A2A1S67S0S23S22VnfP;Vk;A2A1VfaP;A3A3").

Lemma zone_thread : ltac2:(tb__ "0|2|
S0S0S3S1fS1eS86S85VA;A1A1M0Z120A2R1A2S20R1S1eG0Zc60A2A2A2S63VA;Vrb;S4aR3A1R2A4S3S1fS1eS53VA;Vrb;A2Z10A2M1R3A2S20R3S1eG1S21Z4R4A2A2A2A2F_;F_;Fz;Fi;").
Proof.
  intros i z Hz HZ.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A nv)))) as NF0.
  unfold zoneR, phK in HZ. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in HZ. fold nv c in HZ.
  unfold U0, F0, FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, Sh, SHADOW_OFF in HZ. fold nv c in HZ.
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X X2]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; try exact X; exfalso.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG PS1 T1 T2. lia.
  - destruct (HFILLR X2) as (F1 & F2 & F3). unfold gh_nf, gh_new in *. fold nv c in F1, F2, F3, X.
    clear -X Hz F1 F2 F3 HNFP C1 G13 G14 TG PS1 T1 T2. lia.
Qed.

Definition JRpop (i : Z) : jpredA := ltac2:(tb__ "0|3|
S7S27S35Q40M0A1M1A1S27S6bA1S6aS3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVi;A1R4R3R2R1AaS3S2G1S9R4S3dA2S36G0S1eS1eS53VA;Vrb;A2Z10A2S21Z4M2Vi;A2A2A2A3S2G1S9R4S3eA2S36G0S1eS52VA;Vrb;A2S21G2S1eS22VnfP;Vk;A2Vi;A2A2A2A2A3A2A2Lmd;Ltr;Ltp;Lr;").
Lemma JRpop_K : ltac2:(tb__ "0|0|
S0S89VKc;S49R1A1A2Fi;").
Proof. intros i r t tr md [H _]. exact (JR_K A Kc rb tp0 md0 _ r t tr md H). Qed.
Lemma JRpop_stable : ltac2:(tb__ "0|0|
S0S1S2S29S7dS43R1A2S2aA3S48S34R2S49R3A1A3F_;Fn;Fi;").
Proof.
  intros i n Hn r r' tp tr md md' Hag Hme (HJ & H4 & H6). apply Pos.leb_le in Hn. unfold PNX in Hn.
  split; [|split].
  - eapply (JR_stable A Kc rb tp0 md0 (phK i) n HKc); [unfold GR; lia | exact Hag | exact Hme | exact HJ].
  - destruct Hag as (Hw & _). rewrite <- (Hw PV4) by (unfold PV4; lia). exact H4.
  - destruct Hag as (Hw & _). rewrite <- (Hw PV6) by (unfold PV6; lia). exact H6.
Qed.

Definition O_srcc : sobj := ltac2:(tb__ "0|0|
S42S3eS26SeS14SaZ0A1Z4SbS3fA1A3S28SeA1A3A2").
Definition O_dstc : sobj := ltac2:(tb__ "0|0|
S42S3dS26SeS14SaZ0A1Z4S18S2aQ20SbS3fA1A3A3S28SeA1A3A2").

Lemma pop_release : ltac2:(tb__ "0|6|
S1cS27S6A1M0S7S27S35Q40M1A1M2A1S27S6bA1M3S6fS6aS6aS0S3S1fZ0M4R1A2S20R1Vk;A2A2S2G0SfRaA1S30S6R9S26S6S4cS26S6S4bS28S6A1A3A3M5A3A3S1bS34R9RbS2bG3S80R7S81R6R5A2A4A4S2G2S9RaS3fA2S36G1S64S0S23S1eS22VnfP;Vk;A2R4A2A1VfaP;G4A4A2A3S49R5RbRaR9R6A5S6dRcG5R9A3S7S3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aS1eR7Z1A2A1R1RcRbR8AaS3S2G2S9R1S3dA2S9RdS3dA2A3S2G2S9R1S3eA2S9RdS3eA2A3A2A2Tr3;F_;F_;F_;F_;F_;Fi;FmdJ;Fmd;Fms;Ftr;Ftp;Fr2;FK;FS;").
Proof.
  intros S K r2 tp tr ms md mdJ i Hi HO Hsm H7 ((HFz & HGh & HKc' & HM & HR & HRM) & H4 & H6) r3.
  split; [|split; reflexivity].
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _ & _) & _ & (_ & N6) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0) in *.
  assert (Hid : 0 <= idv < 2 ^ 28).
  { apply HIDS. unfold idv. apply nth_In. unfold nfP in *. lia. }
  set (Si := FAb A rb + 4 * (nfP - k + i)) in *. set (Di := PCE A rb + 16 + 4 * i) in *.
  idtac "pr:1".
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  assert (RS : obj_range r2 O_srcc = (Si, Si + 4)).
  { unfold O_srcc, O_cell. rewrite obj_range_mk by lia. cbn [eval]. rewrite H6, u64_lit by (unfold Si in *; lia). f_equal; lia. }
  assert (RD : obj_range r2 O_dstc = (Di, Di + 4)).
  { unfold O_dstc, O_cell. rewrite obj_range_mk by lia. cbn [eval]. rewrite H4, u64_lit by (unfold Di in *; lia). f_equal; lia. }
  set (m2 := view segs (rm r2)) in *. set (m3 := view segs (rm r3)).

  assert (M3S : forall j, (j < 4)%nat -> m3 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. destruct (absorb_obj r2 S tr ms md K [O_srcc; O_dstc] O_srcc Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SVar PV7)) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_srcc O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H6, soff_lit_small, u64_lit in ASb by (unfold Si in *; lia).
    rewrite H7 in ASb. unfold m3. rewrite view_in by (unfold Si in *; lia). fold Si in ASb. replace (Si + 0 + Z.of_nat j) with (Si + Z.of_nat j) in ASb by lia. exact ASb. }
  assert (M3D : forall j, (j < 4)%nat -> m3 (Di + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. destruct (absorb_obj r2 S tr ms md K [O_srcc; O_dstc] O_dstc Hsm HO (or_intror (or_introl eq_refl))) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SExt true 32 (SVar PV7))) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_dstc O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H4, soff_lit_small, u64_lit in ASb by (unfold Di in *; lia).
    rewrite H7, sext32_small in ASb by lia. unfold m3. rewrite view_in by (unfold Di in *; lia). fold Di in ASb. replace (Di + 0 + Z.of_nat j) with (Di + Z.of_nat j) in ASb by lia. exact ASb. }
  assert (M2S : forall j, (j < 4)%nat -> m2 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (HSRC i m2 ltac:(lia) HR (nfP - k + i) ltac:(lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    unfold Si. exact Hc. }
  assert (AGR : forall z, ~ (Di <= z < Di + 4) -> m3 z = m2 z).
  { intros z Hz. destruct (Z_le_dec Si z) as [H1|H1]; [destruct (Z_lt_dec z (Si + 4)) as [H2|H2]|].
    - replace z with (Si + Z.of_nat (Z.to_nat (z - Si))) by lia. rewrite M3S, M2S by lia. reflexivity.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd]; lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd]; lia. }
  idtac "pr:2".
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HKc'|]. split; [exact HM|].
  split; [|apply (rmlink_absorb _ r2 [O_srcc; O_dstc] ms HRM); intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd];
           unfold IMG_LO, IMG_HI, Si, Di; rewrite ?FAr, ?PCr; unfold nfP in *; lia].
  fold m3. unfold rlink in HR |- *. fold m2 in HR.
  destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  assert (ZI : forall z, zoneR A rb (phK (i + 1)) z <-> (zoneR A rb (phK i) z \/ Di <= z < Di + 4)).
  { intros z. unfold zoneR, phK. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. fold nv c. unfold Di. split.
    - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left; left; exact H.
      + left; right; left; exact H.
      + left; right; right; left; exact H.
      + left; right; right; right; left; exact H.
      + left; right; right; right; right; left; exact H.
      + destruct (Z_lt_dec z (PCE A rb + 16 + 4 * i)); [left; right; right; right; right; right; left; lia | right; lia].
      + left; right; right; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; right; right; exact H.
    - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; lia.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
      + right; right; right; right; right; left; lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros z Hz. rewrite AGR by (intros X; apply Hz; apply ZI; right; exact X). apply L1. intros X. apply Hz. apply ZI. left. exact X.
  - intros z Hz. apply ZI in Hz. destruct (Z_le_dec Di z) as [H1|H1]; [destruct (Z_lt_dec z (Di + 4)) as [H2|H2]|].
    + replace z with (Di + Z.of_nat (Z.to_nat (z - Di))) by lia. rewrite M3D by lia. discriminate.
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
  - intros j Hj. cbn [ph_fill phK] in Hj |- *. eapply cell_ok_agree_range; [|exact (L3 j Hj)]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    destruct (HFILLR ltac:(lia)) as (F1 & F2 & F3). unfold Di. rewrite PCr. rewrite FAr in Hz. change (Z.of_nat 4) with 4 in Hz.
    clear -Hz C1 PS1 T1 T2 G13 G14 TG Hj Hi K1 HNFP F1 F2 F3. lia.
  - intros i' Hi'. cbn [ph_pop phK] in Hi'. destruct (Z.eq_dec i' i) as [->|Hne].
    + intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *. fold Di. rewrite M3D by exact Hj. do 3 f_equal. fold nv c. rewrite HCACHE, nth_skipn_Z.
      unfold idv. replace (Z.to_nat (nfP - k) + Z.to_nat i)%nat with (Z.to_nat (nfP - k + i)) by (clear -HKF Hi; lia). reflexivity.
    + eapply cell_ok_agree_range; [|exact (L4 i' ltac:(cbn [ph_pop phK]; lia))]. cbn [c_addr c_w]. intros z Hz. apply AGR. unfold Di. lia.
  - intros X. discriminate X.
  - intros X. discriminate X.
Qed.

Variable F : nat.
Variable CT0 : axst.
Variables LB LX : leafA.
Variable nob : nat.
Variable s_bk : wsub.
Let CT1 : axst := cT1 CT0.
Definition e_end : sv := ltac2:(tb__ "0|0|
ScS4eScS4eS79SaZ10A1A3ScS50S46SaZ2A1A3A3").
Definition NPOP : list carve_spec := ltac2:(tb__ "0|9|
S26S2cS2cS2cS8S0A2M0S0A2M1S27S2cS2cS0S2eA2M2S8A2M3A1M4A2M5S2bG1G4S2bG0S0S2bS8S0SbS3eA1Z0M6A4Z4M7A4S26G3S2bG2S8S2bS0S2eG6U4A4SbS3fA1A4S28G3A1M8A3A4S26G5S2bG1G4S2bG0S0S2bS8S0SbS3dA1G6A4G7A4G8A4S28G5A1A3A3").
Hypothesis SK_t : ltac2:(tb__ "0|1|
S2S27S2cS2cS8S8A2S8A2M0A1S66S6G0S7cSfS38VCT0;A1A1A4S66S6G0S7cS30S6S8bVW;A1S26S6S7aS26S6S7bS26S6S44S26S6S45S28S6A1A3A3A3A3A3A4A3").
Hypothesis XX_t : ax_X CT0 = [].
Hypothesis XF_t : ltac2:(tb__ "0|0|
S69S10S8aVW;Vst;A2S11S38VCT0;A1A1A3").
Hypothesis NX_t : ltac2:(tb__ "0|0|
S2S29S7eS17S38VCT0;A1A1S43A2S2aA3").
Hypothesis W_t1 : ltac2:(tb__ "0|0|
S2S29S1dS38VCT1;A1A1S2aA3").
Hypothesis R_t1 : ltac2:(tb__ "0|1|
S2S2fS27S3aA1M0A1S3cS34VF;S26S0Z413dcS26S0Z413f0S28S0A1A3A3VCT1;S2aA5S31G0S26S3aVLB;S26S3aVLX;S28S3aA1A3A3A2A3").
Hypothesis LN_t1 : ltac2:(tb__ "0|0|
S2S29S16S38VCT1;A1A1S2dA3").
Hypothesis OB_b : ltac2:(tb__ "0|1|
S2S27S6A1SfS38S39VLB;A1A1A1M0S30S6S65S6Vnob;G0A3S26S6S4cS26S6S4bS28S6A1A3A3A3A3").
Hypothesis OB_x : ltac2:(tb__ "0|1|
S2S27S6A1SfS38S39VLX;A1A1A1M0S30S6S65S6Vnob;G0A3S26S6S4cS26S6S4bS28S6A1A3A3A3A3").
Hypothesis ENT_bk : ltac2:(tb__ "0|0|
S2S29S3bS40S39VLB;A1Vnob;A2VCT0;Vs_bk;A3S2aA3").
Hypothesis SID_bk : ltac2:(tb__ "0|0|
S2S29S6eVs_bk;S41A2S2aA3").
Hypothesis S_bk4 : ltac2:(tb__ "0|0|
S2S8S6cVs_bk;S3dA2ScS4eSbS3dA1SaZ4A1A3A3").
Hypothesis S_bk6 : ltac2:(tb__ "0|0|
S2S8S6cVs_bk;S3eA2ScS4eSbS3eA1SaZ4A1A3A3").
Hypothesis FB_b : ltac2:(tb__ "0|0|
S68S10S12S4fScS4eSbS3dA1SaZ4A1A3S4dA3S11S38S39VLB;A1A1A1A3").
Hypothesis FB_x : ltac2:(tb__ "0|0|
S68S10S19S12S4fScS4eSbS3dA1SaZ4A1A3S4dA3A1S11S38S39VLX;A1A1A1A3").

Lemma pop_carve : ltac2:(tb__ "0|5|
S0S7S27S35Q40M0A1M1A1S71S3S1fZ0M2R4A2S20R4Vk;A2A2S47S34S49R5A1VCT0;R4R3R2A6S84R5S26S2cS1G1A2M3S2bS1G1S3fS36G0S64S0S23S1eS22VnfP;Vk;A2M4R6A2A1VfaP;G2A4A2A4S28G3A1A3A2S7S3S47S34S49R7A1VCT1;R1R5R4A6S2G1S9R1S3fA2S36G0S64S0S23S1eG4R7A2A1VfaP;G2A4A2A3A2Tr1;F_;F_;Fw;Ftp;Fr;Fi;").
Proof.
  intros i r tp w Hi H r1.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _ & _) & (_ & MU0 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0) in *.
  assert (E7 : rw r1 PV7 = Z_to_bv 64 idv).
  { unfold r1. apply (rw_rho_sets_in r _ PV7); [repeat constructor; intros [] | left; reflexivity]. }
  split; [|exact E7].
  assert (AG1 : agree_below PNX r r1). { unfold r1. apply agree_below_rho_sets. intros j v [X|[]]. injection X as <- _. unfold PNX, PV7. lia. }
  assert (Erm1 : rm r1 = rm r) by (unfold r1; apply rm_rho_sets).
  assert (H1 : SPA segs (JRpop i) CT0 r1 tp w).
  { destruct H as [Hsm HJ]. split.
    - eapply smatchA_agree; [|exact Hsm]. apply Pos.eqb_eq in NX_t. rewrite NX_t. exact AG1.
    - eapply (JRpop_stable i PNX ltac:(reflexivity)); [exact AG1 | apply mat_equiv_refl | exact HJ]. }
  idtac "pc:1".
  destruct H1 as [HsmA1 HJ1]. pose proof HJ1 as ((HFz & HGh & _ & _ & HR & _) & H4 & H6). pose proof (proj1 HJ1) as HJ1'.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0.
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r1 CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  pose proof (proj1 HsmA1) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CT0) [O_pcc0; O_st; O_pcm; O_ri] r1 _ HW HE HFz Hsm1 SK_t XF_t) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r1 oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r1 os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r1 om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r1 ori O_ri SKr) in RNr.
  set (Si := FAb A rb + 4 * (nfP - k + i)) in *. set (Di := PCE A rb + 16 + 4 * i) in *.
  set (m1 := view segs (rm r1)) in *. unfold rlink in HR. fold m1 in HR.
  assert (ES : bv_unsigned (eval r1 (SVar PV6)) = Si) by (cbn [eval]; rewrite H6; apply u64_lit; unfold Si; lia).
  assert (ED : bv_unsigned (eval r1 (SVar PV4)) = Di) by (cbn [eval]; rewrite H4; apply u64_lit; unfold Di; lia).

  assert (MS : forall j, (j < 4)%nat -> m1 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (HSRC i m1 ltac:(lia) (proj1 (proj2 (proj2 (proj2 (proj2 HJ1'))))) (nfP - k + i) ltac:(lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc. exact Hc. }
  assert (PD : forall z, Di <= z < Di + 4 -> exists b, m1 z = Some b).
  { intros z Hz. destruct HR as (L1 & L2 & _).
    assert (ZD : zoneR A rb (phK i) z \/ ~ zoneR A rb (phK i) z).
    { destruct (Z_lt_dec z (PCE A rb + 16 + 4 * i)) as [Y|Y]; [left; unfold zoneR, phK; cbn [ph_pop]; do 5 right; left; unfold Di in Hz; lia|].
      right. intros X. apply (zone_thread i z) in X; [lia|]. unfold Di in Hz. rewrite PCr in Hz. lia. }
    destruct ZD as [ZD|ZD].
    - specialize (L2 z ZD). destruct (m1 z) as [b|] eqn:Em; [exists b; reflexivity | exfalso; apply L2; first [exact Em | reflexivity]].
    - rewrite (L1 z ZD). destruct HE as (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _).
      destruct (pc_entry_facts0 segs A rb tp0 md0 nv HA Hnv Hcnt) as (_ & PE & _). cbn zeta in PE. fold c in PE. apply PE. unfold Di in Hz. rewrite PCr in Hz. lia. }
  idtac "pc:2".
  assert (SiR : ag_spacebeg (aa_geom A) <= Si /\ Si + 4 <= ag_spacebeg (aa_geom A) + 137438953472) by (unfold Si; rewrite FAr; lia).
  assert (DiR : ag_thread (aa_geom A) + 288 <= Di /\ Di + 4 <= ag_thread (aa_geom A) + 2656) by (unfold Di; rewrite PCr; lia).
  assert (HS1 : SPA segs (JRpop i) CT0 r1 tp w) by (split; [exact HsmA1 | exact HJ1]).
  apply (SPA_carve_list segs _ r1 CT0 tp w NPOP PNX1 HS1 W_t1).
  - apply Pos.eqb_eq in NX_t. rewrite NX_t. unfold PNX, PNX1. lia.
  - unfold NPOP. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + rewrite ES. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [repeat apply Forall_cons; try apply Forall_nil; lia|].
      split.
      { intros off Hoff. rewrite Erm1. specialize (MS (Z.to_nat off) ltac:(lia)). replace (Si + Z.of_nat (Z.to_nat off)) with (Si + off) in MS by lia.
        unfold m1 in MS. rewrite Erm1 in MS. rewrite view_in in MS by lia. eapply wok_rd_off_image; [|exact MS]. lia. }
      split; [|unfold xwords_clear; rewrite XX_t; intros rr y j []].
      apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [eval]. rewrite E7. specialize (MS j Hj). unfold m1 in MS. rewrite view_in in MS by lia.
      replace (Si + 0 + Z.of_nat j) with (Si + Z.of_nat j) by lia. exact MS.
    + rewrite ED. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply Forall_nil|].
      split.
      { intros off Hoff. destruct (PD (Di + off) ltac:(lia)) as [b Hb]. unfold m1 in Hb. rewrite view_in in Hb by lia.
        eapply wok_rd_off_image2; [| |exact Hb]; lia. }
      split; [apply Forall_nil | unfold xwords_clear; rewrite XX_t; intros rr y j []].
  - cbn [map carve_obj NPOP]. unfold carved.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; rewrite obj_range_mk by lia; rewrite ?ES, ?ED; rewrite EO; apply Forall_app; split.
    + apply BZ. right; left. rewrite kSpaceSize_val. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; lia.
    + apply BZ. left. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; unfold Di in *; rewrite ?PCr in *; lia.
  - cbn [map carve_obj NPOP pairwise_disjoint]. unfold carved. split; [|split; [constructor | exact I]].
    apply Forall_cons; [|apply Forall_nil]. rewrite !obj_range_mk by lia. rewrite ES, ED. unfold ranges_disjoint; cbn [fst snd]. lia.
Qed.

Lemma e_end_val : ltac2:(tb__ "0|0|
S7S55Vrb;R1A2S56VA;Vrb;R2A3S2S0S37Q40S13R3S4dA2A2S1eS1eS53VA;Vrb;A2Z10A2S21Z4Vk;A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _).
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  destruct HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _). fold nv c k in Q227.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  unfold e_end, vK. cbn [eval]. rewrite add_val, add_val, sll_val. rewrite EB, Q227, !u64_lit by lia. change (2 mod 64) with 2.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (k * 2 ^ 2)) by lia. rewrite (Z.mod_small (PCE A rb + 16)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition JRrel (i : Z) : jpredA := ltac2:(tb__ "0|3|
S7S27S35Q40M0A1M1A1S27S6bA1S6aS3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aS1eVi;Z1A2A1R4R3R2R1AaS3S2G1S9R4S3dA2S36G0S1eS1eS53VA;Vrb;A2Z10A2S21Z4M2Vi;A2A2A2A3S2G1S9R4S3eA2S36G0S1eS52VA;Vrb;A2S21G2S1eS22VnfP;Vk;A2Vi;A2A2A2A2A3A2A2Lmd;Ltr;Ltp;Lr;").

Lemma pop_iter : ltac2:(tb__ "0|1|
S0S7S27S35Q40A1A1S70S3S1fZ0R4A2S20R4Vk;A2A2S20S1eR5Z1M0A2Vk;A2S7VTR;S47S34S49S1eR7G0A2A1VCT0;R1R5A5R4A2Fr';F_;S2S0S1eR6G0A2Vk;A3S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R6A5R5A2Fr';F_;VTR;S47S34S49R7A1VCT0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;").
Proof.
  intros i r tp Q Hi HKb HKx.
  assert (NUM : 0 <= PCE A rb /\ PCE A rb + 16 + 4 * k + 8 < 2 ^ 62 /\ 1 <= k <= 8).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
    destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & _ & (T1 & T2 & _) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia. }
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0).
  set (r1 := rho_sets r [(PV7, Z_to_bv 64 idv)]).
  assert (E7 : rw r1 PV7 = Z_to_bv 64 idv).
  { unfold r1. apply (rw_rho_sets_in r _ PV7); [repeat constructor; intros [] | left; reflexivity]. }
  apply (tr_pre Kc TR KIT (SPA segs (JRpop i) CT1 r1 tp)); [intros w Hw; exact (proj1 (pop_carve i r tp w Hi Hw))|].
  apply (tr_run Kc TR KIT F [0x413dc; 0x413f0] CT1 [LB; LX] (JRpop i) r1 tp Q (JRpop_K i) (JRpop_stable i (ss_next (ax_S CT1)) eq_refl) R_t1 LN_t1).
  intros L r2 HL Hag.
  assert (NX1 : ss_next (ax_S CT1) = PNX1) by reflexivity. rewrite NX1 in Hag.
  assert (E72 : rw r2 PV7 = Z_to_bv 64 idv) by (destruct Hag as (Hw & _); rewrite <- (Hw PV7) by (unfold PV7, PNX1; lia); exact E7).

  assert (REL : forall (LL : leafA), ss_objs (ax_S (la_state LL)) = firstn nob (ss_objs (ax_S (la_state LL))) ++ [O_srcc; O_dstc] ->
            forall w, SPA segs (JRpop i) (la_state LL) r2 tp w -> exists r3, SPA segs (JRrel i) (keepn (la_state LL) nob) r3 tp w).
  { intros LL HO [tr [ms md]] Hw. exists (rho_absorb r2 [O_srcc; O_dstc] (vms md tp ms)).
    apply (SPA_unobj_J (JRpop i) (JRrel i) r2 (la_state LL) _ [O_srcc; O_dstc] tp tr ms md HO Hw).
    intros Hsm HJ. pose proof HJ as (_ & H4 & H6).
    destruct (pop_release (ax_S (la_state LL)) _ r2 tp tr (vms md tp ms) (vmd md) md i Hi HO Hsm E72 HJ) as (P1 & P2 & P3). cbn zeta in P1, P2, P3.
    split; [exact P1|]. split; [rewrite P2; exact H4 | rewrite P3; exact H6]. }
  destruct HL as [<-|[<-|[]]].
  -
    apply (tr_facts Kc TR KIT). intros HF.
    pose proof (proj1 (Forall_forall _ _) HF _ FB_b) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 < k)).
    { intros w [_ ((HFz & HGh & _) & H4 & _)]. unfold branch_taken, bv_eqb in BF. apply negb_true_iff in BF. apply Z.eqb_neq in BF.
      rewrite (e_end_val r2 HFz HGh) in BF. cbn [eval] in BF. rewrite add_val, H4, !u64_lit in BF by lia.
      rewrite Z.mod_small in BF by lia. lia. }
    intros Hlt.
    apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRrel i) (keepn (la_state LB) nob) r3 tp) Q (REL LB OB_b)).
    intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRpop (i + 1)) CT0 (rho_sub r3 s_bk) tp)); [|exact (HKb Hlt _)].
    intros w Hw. apply (SPA_entails_J (JRrel i) (JRpop (i + 1)) _ CT0 s_bk r3 tp w ENT_bk); [|exact Hw].
    intros (HJ & H4 & H6). pose proof (rho_sub_agree s_bk GR r3 SID_bk) as AGs.
    split; [|split].
    + eapply (JR_stable A Kc rb tp0 md0 (phK (i + 1)) GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    + cbn [rho_sub rw]. rewrite S_bk4. cbn [eval]. rewrite H4. apply bv_eq. rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
    + cbn [rho_sub rw]. rewrite S_bk6. cbn [eval]. rewrite H6. apply bv_eq.
      assert (FAR : 0 <= FAb A rb /\ FAb A rb + 536870912 + 8 < 2 ^ 62).
      { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
        destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
        unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
      rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
  -
    apply (tr_facts Kc TR KIT). intros HF.
    pose proof (proj1 (Forall_forall _ _) HF _ FB_x) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 = k)).
    { intros w [_ ((HFz & HGh & _) & H4 & _)]. unfold branch_taken, bv_eqb in BF. apply not_true_is_false in BF. apply negb_false_iff in BF. apply Z.eqb_eq in BF.
      rewrite (e_end_val r2 HFz HGh) in BF. cbn [eval] in BF. rewrite add_val, H4, !u64_lit in BF by lia.
      rewrite Z.mod_small in BF by lia. lia. }
    intros Heq.
    apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRrel i) (keepn (la_state LX) nob) r3 tp) Q (REL LX OB_x)).
    intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRp (phK k)) (keepn (la_state LX) nob) r3 tp)); [|exact (HKx Heq _)].
    intros w Hw. apply (SPA_J (JRrel i) (JRp (phK k)) _ r3 tp w); [|exact Hw]. intros (HJ & _). rewrite <- Heq. exact HJ.
Qed.

Lemma pop_loop : ltac2:(tb__ "0|0|
S2eS0S7S27S35Q40A1A1S70S2S0S22Vk;R4A2S24R5A1A3S3S1fZ0R5A2S20R5Vk;A2A2S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R5A5R4A2Fr';VTR;S47S34S49R7A1VCT0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;Fn;").
Proof.
  induction n as [|n IH]; intros i r tp Q Hn Hi HX; [lia|].
  apply (pop_iter i r tp Q Hi).
  - intros Hlt r'. apply (IH (i + 1) r' tp Q); [lia | lia | exact HX].
  - intros _ r'. apply HX.
Qed.

Variable J0 : axst.
Variable LT0 : leafA.
Variable s_in : wsub.
Variable e_src : sv.
Hypothesis R_t0 : ltac2:(tb__ "0|1|
S2S2fS27S3aA1M0A1S3cS34VF;S26S0Z413dcS26S0Z413f0S28S0A1A3A3VJ0;S2aA5S31G0S26S3aVLT0;S28S3aA1A3A2A3").
Hypothesis LN_t0 : ltac2:(tb__ "0|0|
S2S29S16S38VJ0;A1A1S2dA3").
Hypothesis NX_t0 : ltac2:(tb__ "0|0|
S2S29S7dS41S17S38VJ0;A1A1A2S2aA3").
Hypothesis ENT_in : ltac2:(tb__ "0|0|
S2S29S3bS39VLT0;A1VCT0;Vs_in;A3S2aA3").
Hypothesis SID_in : ltac2:(tb__ "0|0|
S2S29S6eVs_in;S41A2S2aA3").
Hypothesis S_in4 : ltac2:(tb__ "0|0|
S2S8S6cVs_in;S3dA2ScS4eS79SaZ10A1A3A3").
Hypothesis S_in6 : ltac2:(tb__ "0|0|
S2S8S6cVs_in;S3eA2Ve_src;A3").
Hypothesis HSRCP : ltac2:(tb__ "0|1|
S7S55Vrb;R1A2S56VA;Vrb;R2A3S2S35Q40M0A1S13R3Ve_src;A2S36G0S1eS52VA;Vrb;A2S21Z4S22VnfP;Vk;A2A2A2A2A3F_;F_;Fr;").

Lemma phK0 : phK 0 = ph.
Proof.
  destruct PH0 as (P1 & P2 & P3).
  transitivity (mkPh (ph_u ph) (ph_f ph) (ph_fill ph) (ph_pop ph) (ph_cnt ph) (ph_ri ph)); [unfold phK; rewrite P1, P2, P3; reflexivity | symmetry; apply ph_eta].
Qed.

Lemma pop_all : ltac2:(tb__ "0|0|
S7S27S35Q40A1A1S70S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R3A5R2A2Fr';VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VJ0;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HX.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x413dc; 0x413f0] J0 [LT0] ph r tp Q R_t0 LN_t0 NX_t0).
  intros L r1 [<-|[]] _.
  assert (K1 : 1 <= k).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & (K1 & _) & _). fold k in K1. lia. }
  apply (tr_pre Kc TR KIT (SPA segs (JRpop 0) CT0 (rho_sub r1 s_in) tp)); [|apply (pop_loop (Z.to_nat k) 0 _ tp Q); [lia | lia | exact HX]].
  intros w Hw. apply (SPA_entails_J (JRp ph) (JRpop 0) _ CT0 s_in r1 tp w ENT_in); [|exact Hw].
  intros HJ. pose proof (rho_sub_agree s_in GR r1 SID_in) as AGs. pose proof HJ as (HFz & HGh & _).
  split; [|split].
  - rewrite phK0. eapply (JR_stable A Kc rb tp0 md0 ph GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
  - cbn [rho_sub rw]. rewrite S_in4. cbn [eval].
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    destruct (arm_extra_ranges A rb r1 CF0 RG HGh) as (EB & _).
    apply bv_eq. rewrite add_val, EB, !u64_lit.
    + rewrite Z.mod_small; [lia|]. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
      destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _). pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia.
    + unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
      destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _). pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia.
    + lia.
  - cbn [rho_sub rw]. rewrite S_in6. rewrite (HSRCP r1 HFz HGh). f_equal. lia.
Qed.
End POP.
End SpineCallocR3.

(* [comment removed for export] *)
Module SegQ3D_qiq.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "cons"; "list"; "bool"; "nat"; "app"; "nil"; "true"; "false"; "option"; "None"; "andb"; "fst"; "S"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SVar"; "rm"; "valuation"; "SAlu"; "SLit"; "sprop"; "ss_objs"; "ss_facts"; "eval"; "ob_dflt"; "obj_range"; "odefault"; "rl"; "rw"; "SExt"; "dflt_writable"; "ranges_disjoint"; "swf"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "add"; "opp"; "sub"; "leb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_setS"; "axst"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "mkQB"; "aa_cache_inited"; "aa_geom"; "aa_q_global"; "aa_q_thread"; "qb_addr"; "qb_items"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs"; "TQ2"; "KEPTQ"; "TQ1"; "TQ3"; "RIr"; "TQIf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "vIT"; "F_DI"; "O_it"; "vS7"; "@Stdlib.Lists.List"; "forallb"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_SLL"; "ALU_SRL"; "ALU_XOR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "O_sb"; "add"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq"; "RQP"; "NRO"; "rieS"; "spec_litb"; "FTLQ"; "N_itmP"; "cptrQ"; "entS"; "hdrS"; "hideP"; "hwP"; "magS"; "slotS"; "stqS"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "N_rti"; "entQ"; "O_ishQ"; "qienv"; "rieQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "HVI"; "HVS"; "addo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "HVX"; "with_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel"; "FRM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "O_mtx00"; "STK"; "SWD"; "cb_cells"; "vXF"; "vXK"; "vXL"; "vXS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "O_gmax"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "it_ab"; "it_cls"; "it_id"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "batch_mem"; "item_mem"; "QFP"; "QRD"; "batch_pure"; "push_cache"; "set_q"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep";
"set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue"; "coverb"; "spec_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith"; "vb_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma FRM_absorb_gen : ltac2:(tb__ "0|7|
S40S17S17S17S0OF_;S0S2bR2R1A1M0S2aG0A1A2Fz;S1S28S3cQ40M1A1M2S22R4R1A2S22R5R1A2A3Fi;S1S28S5S3cQ8A1M3A1S21R5R1A2S21R6R1A2A3Fl;S0R5R1A1S2bS94RaR2A2S29S95RaR2A2S28ScG3A1M4S48S37S16R7A1R2A3S48S37S16R8A1R2A3A3A2A2F_;Fz;G2R6S3eG1R1A2M5A1S29S2fS9dS3eG1R2A2M6A2S30G6S9cA2A2S2aS28G4S16R9R3A2SdG3A1A3A1F_;F_;Fa;S0S2aR7R1A1A1S28G4S48S37S16R9A1R2A3S48S37S16RaA1R2A3A3F_;Fz;G2S2aR8G5A1A1S28G4S16RaR2A2S16RbR2A2A3F_;Fa;S83RcRbRaA3S83RdRcRaA3F_;F_;F_;F_;F_;F_;F_;F_;FP;Frho3;Frho;Frho0;FA0;").
Proof.
  intros A0 rho0 rho rho3 P PD Hrw Hrl HP HB FR FRrm ((F1 & F1') & F2 & F3 & F4).
  split; [split; [intros i Hi; rewrite Hrw; exact (F1 i Hi) | intros l; rewrite Hrl; exact (F1' l)]|]. split; [|split].
  - intros a NQ. rewrite FRrm; [exact (F2 a NQ)|]. intros Hp. apply NQ. destruct (HP _ Hp) as [HQ|[HQ _]]; [left; exact HQ | exact HQ].
  - intros z NQ. rewrite <- (F3 z NQ). destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. destruct (HP z Hp) as [HQ|[_ HE]]; [exfalso; exact (NQ HQ) | exact HE].
  - intros a HBa Hdef. destruct (PD (bv_unsigned a)) as [Hp|Np]; [exact (HB a Hp HBa) | rewrite (FRrm a Np); exact (F4 a HBa Hdef)].
Qed.

Lemma item_mem_frameP : ltac2:(tb__ "0|4|
S49S49S2S0S0A2S2fZ10S9eS12S0S0R1A3A1A2S0S29S2fS8eR3A1R1A2S30R1SfS0S0R3A3A2A2S28ScS3cQ8A1M0A1M1R5R2A1R6R2A1M2A3F_;Fz;S0S2aS28G1R6R1A1SdG0A1M3A3A1S2aS28G1G2G3A3A1F_;Fz;S93R6R4A2S93R6R5A2F_;F_;F_;F_;Fit;Fm';Fm;").
Proof.
  intros m m' it Hrz HL HP (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold it_ab in HL.
  split; [rewrite HL by lia; exact H1|]. split; [eapply present_frame; [|exact H2]; intros z Hz; apply HL; lia|].
  split; [eapply cell_ok_frame1; [|exact H3]; cbn; intros z Hz; apply HL; lia|].
  split; [eapply cell_ok_frame1; [|exact H4]; cbn; intros z Hz; apply HL; lia|].
  split; [eapply present_frame; [|exact H5]; intros z Hz; apply HL; lia|].
  split.
  - unfold alloc_magic_ok in *. destruct H6 as [H6|[H6a H6b]]; [left; exact H6 | right].
    split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply HL; lia.
  - intros z Hz. destruct (H7 z Hz) as [b Hb]. pose proof (HP z ltac:(rewrite Hb; discriminate)) as X.
    destruct (m' z) as [b'|]; [exists b'; reflexivity | exfalso; exact (X eq_refl)].
Qed.
Lemma batch_mem_frameP : ltac2:(tb__ "0|5|
S40S49S49S3fS96R4R1A2S0S29S2fS32S46R3A1M0Z8A2R1A2S30R1S32G0Z2000A2A2A2S28ScS3cQ8A1M1A1M2R5R2A1R6R2A1A3F_;Fz;S2S0S0A2M3S0S59G3R2S47R5A1A3S29S2fS8eR3A1R2A2S30R2SfS0S0R3A3A2A2S28G2R8R3A1R9R3A1A3F_;F_;Fz;Fit;S0S2aS28G2R7R1A1SdG1A1M4A3A1S2aS28G2R7R2A1G4A3A1F_;Fz;S92R7R5A2S92R7R6A2F_;F_;F_;F_;F_;Fb;Fm';Fm;FA;").
Proof.
  intros A m m' b (_ & HLn & _ & HPu) HB HI HP (H1 & H2 & H3 & H4 & H5). unfold kQuarantineBatchCount in HLn.
  split; [eapply cell_ok_frame1; [|exact H1]; cbn; intros z Hz; apply HB; lia|].
  split; [eapply cell_ok_frame1; [|exact H2]; cbn; intros z Hz; apply HB; lia|].
  split; [exact H3|]. split; [eapply present_frame; [|exact H4]; intros z Hz; apply HB; unfold kQuarantineBatchSize in Hz; lia|].
  intros i it Hi. destruct (H5 i it Hi) as [C I]. pose proof (nth_error_In _ _ Hi) as Hin.
  assert (Hi' : (i < length (qb_items b))%nat) by (apply (proj1 (nth_error_Some (qb_items b) i)); rewrite Hi; discriminate).
  split.
  - eapply cell_ok_frame1; [|exact C]. cbn. intros z Hz. apply HB. lia.
  - eapply item_mem_frameP; [apply (proj1 (rz_facts (snd it))) | intros z Hz; exact (HI it z Hin Hz) | exact HP | exact I].
Qed.

Lemma head_item_fresh : forall {X Y : Type} (f : X -> Y) (p : X -> bool) (x : X) (l : list X),
  NoDup (map f (List.filter p (x :: l))) -> p x = true -> ~ In x l.
Proof.
  intros X Y f p x l ND Hp Hin. cbn [List.filter] in ND. rewrite Hp in ND. cbn [map] in ND. inversion ND as [|y0 l0 NI ND']; subst.
  apply NI. apply list_elem_of_In. apply in_map. apply filter_In. split; [exact Hin | exact Hp].
Qed.

Lemma absorb_io : ltac2:(tb__ "0|3|
S17S5S14A1S99S29S3cQ40M0A1S2aS5eR4R3R1A3A1S28ScS3cQ8A1A1M1S16S5fR5R4R3A3M2R2A2S16R5R2A2A3F_;Fa;S0S2aS29S29S2fZ0R1A2S30R1S31Z2Z40A2A2A2S5eR4R3S3dG0R1A2A3A2A1S28G1S48S37S16G2A1R2A3S48S37S16R5A1R2A3A3F_;Fz;A2Fms;FR;Frho;").
Proof.
  intros rho R ms. split; [intros a Ha; apply rm_absorb_out; exact Ha|].
  intros z Hz. apply view_agree. intros Hr. apply rm_absorb_out. intros Hin. apply Hz. split; [exact Hr | exact Hin].
Qed.
Lemma IRdec : ltac2:(tb__ "0|1|
S17S5S14A1S0S2bS29S29S2fZ0R1A2S30R1S31Z2Z40A2A2A2S5eR3R2S3dQ40R1A2A3A2M0S2aG0A1A2Fz;FR;Frho;").
Proof.
  intros rho R z. destruct (in_ranges_dec rho R (Z_to_bv 64 z)) as [H|H]; [|right; intros [_ X]; exact (H X)].
  destruct (Z_le_dec 0 z) as [L|L]; [destruct (Z_lt_dec z (2 ^ 64)) as [L2|L2]|]; [left; split; [lia | exact H] | right; intros [X _]; lia | right; intros [X _]; lia].
Qed.

Lemma carve_slot_it : ltac2:(tb__ "0|5|
S53S3bS17S5S3cQ40M0A1M1A1S74S0S0S52S37R7R6R5R4R3A6S28S5S2S13S13A2M2A1S39R7A1S9G2A1A3S28S6S26S82S38R8A1S56A2A1SaA3S28G1S1dR8S57A2S3dG0R5A2M3A3S28G1S1dR9S54A2G3A3S2fS32Z646000Z80M4A2R7A2S2fR8S31Z2Z3eA2A2S4aS48S37S16RcA1A2S4bS34R9G4A2U8R8A3A2S72S14S14S25S1fReR1A2S3S0S0S34RbG4A2S34RbZ78A2A4A2Lo';S1bS38ReA1A1A3S52S37R10S3aRfS82S38RfA1S56A2A2ReRdRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmm;FB;Fw;Ftp;Frho;FS0;FJ;").
Proof.
  intros J S0 rho tp w B mm H HX Hswf Ee Em HB1 HB2 Cm HD.
  pose proof (SPA_carve_list segsA J rho S0 tp w [(vS7, -128, -120, [(-128, 8%nat, vIT)])] (ss_next (ax_S S0)) H) as X.
  cbn zeta in X. cbn [map carve_obj] in X. apply X; clear X.
  - exact Hswf.
  - apply Pos.le_refl.
  - apply Forall_cons; [|apply Forall_nil]. rewrite Ee, u64_lit by lia.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
    split; [|split].
    + intros off Hoff. replace (B + off) with (B - 128 + (off + 128)) by lia. eapply (cell_wok_rd _ _ _ _ _ Cm); cbn [Z.of_nat]; lia.
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      eapply (civ_cell rho (rm rho) B (-128)); [replace (B + -128) with (B - 128) by lia; exact Cm | exact Em | lia | lia].
    + intros rr y j Hin. rewrite HX in Hin. destruct Hin.
  - apply Forall_cons; [|apply Forall_nil]. unfold O_it, carved in *.
    assert (ER : forall cs, obj_range rho (mkObj vS7 (SLit (-128)) (SLit (-120)) cs DUnknown) = (B - 128, B - 120)).
    { intros cs. rewrite obj_range_mk by lia. rewrite Ee, u64_lit by lia. f_equal; lia. }
    rewrite ER. exact HD.
  - cbn [pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Lemma carve_obj_range : ltac2:(tb__ "0|4|
S17S2dS2S2S2S13S0A2M0S0A2M1S5S2S2S0S7A2S13A2A1M2A2OLk;R1G1G2G1OLp;R2G0S0G0OLp0;R2S13S0S29S2fS33S31Z2Z3eA2M3A1R1A2S29S2fR1R3A2S30R3G3A2A2A2Llo;Ls;X2x1Lhi;Lp0;X2x1Ll;Lp;X2x1S28S2S0S0A2S1fR3S2eR2A1A2Sa0R3R2A2A3F_;Fk;Frho;").
Proof. intros rho [[[b lo] hi] cs] (H1 & H2 & H3). cbn [carve_obj SMGlue.spec_range]. unfold carved. rewrite obj_range_mk by lia. reflexivity. Qed.

Definition hwP : sv := ltac2:(tb__ "0|0|
S18S5dS23SaQ20S15PcbA1A3S19Z3A1A3").
Definition cptrQ (vb : bool) : sv := ltac2:(tb__ "0|0|
S18S5cS18S5aS18S5aS6S13Lvb;Vvb;S15Pd2A1S54X6x2S18S5bS15Pc8A1S19Z20A1A3A3S62A3S19Z4A1A3").
Definition rieS : carve_spec := ltac2:(tb__ "0|4|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S7dZ30M3A4Z38A4S4G2S3G1S13S3S0S7G3U8A4S15PcaA1A4S9G2A1A3A4").
Definition entS : carve_spec := ltac2:(tb__ "0|5|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S7aZ0M3A4Z10A4S4G2S3G1S13S3S0S7G3U4M4A4S61S15PceA1S19Z1A1A2A4S4G2S3G1S13S3S0S7Z4G4A4S15PcfA1A4S4G2S3G1S13S3S0S7Z8U8A4S15Pc9A1A4S9G2A1A3A3A3A4").
Definition slotS (vb : bool) : carve_spec := ltac2:(tb__ "0|4|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S61S7aS18S5bS15PceA1S19Z2A1A3A2Z10M3A4Z14A4S4G2S3G1S13S3S0S7G3U4A4S69Vvb;A1A4S9G2A1A3A4").
Definition hdrS : carve_spec := ltac2:(tb__ "0|5|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S54Z0M3A4Z8A4S4G2S3G1S13S3S0S7G3U4M4A4S6dA4S4G2S3G1S13S3S0S7Z4G4A4S15PccA1A4S9G2A1A3A3A4").
Definition stqS : carve_spec := ltac2:(tb__ "0|3|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S9bZad0A4Zc60A4S4G2S3G1S13S3S0S7Zae0U8A4S61S15Pd1A1S18S5aS19Z0A1S15Pc9A1A3A2A4S9G2A1A3A4").
Definition magS : carve_spec := ltac2:(tb__ "0|5|
S3S2S2S13S0A2M0S0A2S5S2S2S0S7A2M1S13A2M2A1S3G0S0S3S13S0S15Pd2A1Z0M3A4Z10A4S4G2S3G1S13S3S0S7G3U8M4A4S19G3A1A4S4G2S3G1S13S3S0S7Z8G4A4S54A4S9G2A1A3A3A4").
Definition N_itmP (vb : bool) : list carve_spec := ltac2:(tb__ "0|1|
S8S2dS4S2dS6bS4S2dS6aS4S2dS6fVvb;A1S4S2dS70S9S2dA1M0A3A3A3A3S6S5S2dA1Lvb;Vvb;S4S2dS6eG0A3G0X6x2A3").
Definition NRO : list carve_spec := ltac2:(tb__ "0|0|
S8S2dS79S4S2dS65S9S2dA1A3A3").
Definition RQP (vb : bool) : list sobj := ltac2:(tb__ "0|0|
S8S14S71S2dS14S2eS79A4S8S14S4S14S7bS4S14S2eS65A1S9S14A1A3A3S71S2dS14S2eS68Vvb;A1A4A3A3").
Lemma TQ1_objsP : ltac2:(tb__ "0|0|
S6S28S5S14A1S1bS38S4eR1A1A1A1S8S14S4dS63R1A1A3A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TQ2_eq : ltac2:(tb__ "0|1|
S6S28S3bS3aS4eR1A1M0S9aS38G0A1S4dA2A2S4cR1A1A3Fvb;"). Proof. intros vb. reflexivity. Qed.
Definition FTLQ (vb : bool) : list sprop := ltac2:(tb__ "0|0|
S73S1aS11S1aS55A2S1cS38S4fVvb;A1A1A1A3").
Lemma TQ3_facts : ltac2:(tb__ "0|2|
S6S29S28S5S1aA1M0S1cS38S4cR1A1A1A1S8S1aS55S67R1A1A3M1A3S28G0S1cS38S4fR1A1A1A1G1A3A2Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma F_DI_pre : ltac2:(tb__ "0|1|
S2cS5S1aA1M0G0S28G0S55S8S1aS76S8dA1R1A3A3LF;A2"). Proof. eexists. reflexivity. Qed.
Lemma TQ2_objs : ltac2:(tb__ "0|1|
S6S28S5S14A1S1bS38S4cR1A1A1A1S8S14S8S14S85S87S86S89S88S8aS8bA4A2S4S14S84S4S14S8cS9S14A1M0A3A3A3S8S14S75G0A3A3A3Fvb;"). Proof. intros [|]; reflexivity. Qed.
Lemma TQ2a_objs : ltac2:(tb__ "0|1|
S6S28S5S14A1S1bS38S80S4cR1A1S60A2A1A1S8S14S8S14S85S87S86S89S88S8aS8bA4A2S4S14S84S4S14S8cS9S14A1M0A3A3A3S8S14S75S4S14S60G0A3A3A3A3Fvb;"). Proof. intros [|]; reflexivity. Qed.
Lemma TQ2_X : ltac2:(tb__ "0|4|
S6S29S28S5S2S13S13A2M0A1M1S39S4cR1A1M2A1S9G0A1M3A3S28G1S39S80G2S60A2A1G3A3A2Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma NRO_chk : ltac2:(tb__ "0|0|
S28S6S58S2dS9fS64A3SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RQP_unk : ltac2:(tb__ "0|1|
S6S28S6S58S14S14S20S6Lx;S1eR1A1SaSbSbS1SbLl;M0G0S0S13S5S2S0S0A2A1S5S27A1SbLtmpl;Lflds;Lcnt;Lesz;X20x6Lo;S63R1A1A3SaA3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RQP_wr : ltac2:(tb__ "0|0|
S6S28S6S58S14S14S24S1eR1A1A1Lo;S63R1A1A3SaA3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition spec_litb (k : carve_spec) : bool := ltac2:(tb__ "0|4|
S2S2S2S13S0A2M0S0A2M1S5S2S2S0S7A2S13A2A1M2A2S6Lk;Vk;G1G2G1S6Lp;R2G0S0G0S6Lp0;R2S13S0SeSeS35S33S31Z2Z3eA2M3A1R1A2S35R1R3A2A2S36R3G3A2A2Llo;Ls;X2x1Lhi;Lp0;X2x1Ll;Lp;X2x1").
Lemma NRO_lit : ltac2:(tb__ "0|0|
S28S6S58S2dS66S64A3SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma spec_litb_sound : ltac2:(tb__ "0|4|
S2dS28S6S66R1A1SaA3S2S2S2S13S0A2M0S0A2M1S5S2S2S0S7A2S13A2A1M2A2OLk;R2G1G2G1OLp;R2G0S0G0OLp0;R2S13S0S29S2fS33S31Z2Z3eA2M3A1R1A2S29S2fR1R3A2S30R3G3A2A2A2Llo;Ls;X2x1Lhi;Lp0;X2x1Ll;Lp;X2x1F_;Fk;").
Proof. intros [[[b lo] hi] cs] H. unfold spec_litb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia. Qed.
Definition hideP (P : Prop) : Prop := P.
Lemma hideP_intro : ltac2:(tb__ "0|0|
OR1S6cR2A1F_;FP;"). Proof. intros P x. exact x. Qed.

Section QIPost.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Hypothesis HSBD : KQ_secband K.
Variables (A0 : AA) (rho0 : valuation).
Variables (A : AA) (it : Z * Z).
Local Notation qT := (ag_thread (aa_geom A)).
Local Notation qSB := (ag_spacebeg (aa_geom A)).
Local Notation qc := (it_cls it).
Local Notation qk := (Z.of_nat (length (cs_cache (cls_of A (it_cls it))))).
Local Notation qu := (fst it).
Local Notation qab := (fst it - rz (snd it)).
Local Notation qLEN := ((snd it + 7) / 8 * 8 / 8).
Local Notation qE := (ag_thread (aa_geom A) + 208 + 80 * it_cls it).

Lemma qi_post : ltac2:(tb__ "0|3|
S0S0S0S7S5S2S0S0A2M0A1S5S3fA1M1G1S17S5S3cQ40A1A1S74S0S0S28G1S45VA;A1S9S3fA1M2A3S28S6S42VA;A1SaA3S0S91VA;R1A2S91VA0;R2A2F_;Fz;S78VA0;VA;A2S28G1S44VA;A1S4S3fS41R10S4G0Vit;RcA3RfA3S8S3fRbRaA3A3A3S52S37S77VK;VA0;Vrho0;VA;R11RfReS4G0Vit;RdA3RcRbAaS51Sa1Vit;A1A1RaR9R8A6S7cVA;Vit;RbR8R7A5S81RcReA2S7eRdR14R12R11Vit;A5S7fReR15R12Vit;A4S2cS17S17S29S52S37S77VK;VA0;Vrho0;S97S98VA;G2S4S3fS41R17R13R16A3S8S3fR12R11A3A3A3S8fVit;A1S90S43VA;A1Vit;A2A3R17R15S10R14A1R13R12R11AaS50R1RfReA6S29S81R1R12A2S29S7eR1R17R15R14Vit;A5S7fR1R17R14Vit;A4A2A2A2Lrho5;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Ft;Fw;Ftp;Frho;Frest;Ftmp';Fits;Fnd;Fn0;Fs;Fa;").
Proof.
  intros a s n0 nd its tmp' rest rho tp w t st HTH HCI HQW HQP0 HGL H QE HVx HVi HVs. destruct w as [tr [ms md]].
  remember (vb_of it) as vb eqn:EVB.
  pose proof (SPA_axforms segsA _ _ rho _ _ tp _ (TQ1_eq vb) H) as H1.
  destruct (proj2 H1) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H1)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE. pose proof BE as [_ _ _ HAU _ _ _].
  pose proof (HSBD A rho tp tr md HK) as HSECB.

  pose proof QE as [_ _ _ _ QGEO QV QCV QIM _ _ _ QNF _ _ QIN QPR _]. unfold qgeo in QGEO. unfold it_ab in QGEO.
  destruct QGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  destruct HRIG as (E151 & E152 & E155 & E156).
  destruct QV as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
  pose proof (qe_nums A it rho t st QE) as NUMS. cbv zeta in NUMS. destruct NUMS as (T0 & T1 & C0 & C1' & S14 & TG & K16).
  pose proof (qe_Sh A it rho t st QE) as SHF. cbv zeta in SHF. destruct SHF as (SH0 & SH1 & L0 & L1).
  pose proof (qe_E A it rho t st QE) as EVS. cbv zeta in EVS. unfold it_ab in EVS. destruct EVS as (EvT & EvC & EvIT & Erie & Eent & Eslot & Esh & Elen & E210u).
  pose proof (qe_wins A it rho t st QE) as WINS. cbv zeta in WINS. apply hideP_intro in WINS.
  pose proof (ish_range A it rho t st QE) as RG_ish. cbv zeta in RG_ish.
  pose proof (cv_max _ _ _ _ _ QCV) as C_max. pose proof (cv_size _ _ _ _ _ QCV) as C_sz. unfold pc_entry in C_max, C_sz.
  pose proof HCB as (_ & HN0 & HN1 & _). unfold kQuarantineBatchCount in HN1. cbn [length] in HN0.
  assert (INB : In (mkQB a (it :: its) s) (aa_q_global A)) by (rewrite HGL; left; reflexivity).
  destruct (batch_addr_facts A HTH rho _ BE INB) as (BA1 & BA2 & BA3 & BA4 & BA5). cbn [qb_addr] in BA1, BA2, BA3, BA4, BA5. unfold HIGH_SHADOW_END in BA4.
  pose proof HQP0 as (ESB & _). assert (EG : aa_geom A = aa_geom A0) by (unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  assert (HVB : vb = true -> rz (snd it) <> 16) by (rewrite EVB; unfold vb_of; intros X; apply negb_true_iff in X; apply Z.eqb_neq in X; exact X).
  assert (HVBf : vb = false -> rz (snd it) = 16) by (rewrite EVB; unfold vb_of; intros X; apply negb_false_iff in X; apply Z.eqb_eq in X; exact X).
  pose proof (carve_rti A it rho t st QE) as CRTI.
  pose proof (carve_itm A it rho t st QE) as CITM. cbv zeta in CITM. specialize (CITM vb HVB). unfold N_itm in CITM. cbn [app] in CITM. pose proof (Forall_inv CITM) as CRIE. clear CITM.
  set (R := RQP vb). set (rho3 := rho_absorb rho R (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.

  assert (RG_hdr : obj_range rho (carve_obj hdrS) = (qu - 16 + 0, qu - 16 + 8)) by (unfold hdrS, carve_obj, carved; rewrite obj_range_mk by lia; rewrite EvIT; reflexivity).
  assert (RG_ent : obj_range rho (carve_obj entS) = (qE + 0, qE + 16)) by (unfold entS, carve_obj, carved; rewrite obj_range_mk by lia; rewrite Eent; reflexivity).
  assert (RG_slot : obj_range rho (carve_obj (slotS vb)) = (qE + 4 * qk + 16, qE + 4 * qk + 20)) by (unfold slotS, carve_obj, carved; rewrite obj_range_mk by lia; rewrite Eslot; reflexivity).
  assert (RG_stq : obj_range rho (carve_obj stqS) = (qT + 2768, qT + 3168)) by (unfold stqS, carve_obj, carved; rewrite obj_range_mk by lia; rewrite EvT; reflexivity).
  assert (RG_mag : obj_range rho (carve_obj magS) = (qab + 0, qab + 16)) by (unfold magS, carve_obj, carved; rewrite obj_range_mk by lia; rewrite E210u; reflexivity).
  set (RNG := fun z : Z => (exists k0, In k0 NRO /\ fst (SMGlue.spec_range rho k0) <= z < snd (SMGlue.spec_range rho k0))
                \/ (Sh qu <= z < Sh qu + qLEN) \/ (qu - 16 <= z < qu - 8) \/ (qE <= z < qE + 16)
                \/ (qE + 4 * qk + 16 <= z < qE + 4 * qk + 20) \/ (qT + 2768 <= z < qT + 3168) \/ (vb = true /\ qab <= z < qab + 16)).
  assert (IRC : forall x, in_ranges rho R x -> RNG (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold RNG. unfold R, RQP in Ho. apply in_app_or in Ho as [Ho|Ho].
    - apply in_map_iff in Ho as (k0 & <- & Hk0). left. exists k0.
      assert (Hk0' : In k0 NRO) by (unfold NRO; apply in_or_app; left; exact Hk0). split; [exact Hk0'|].
      rewrite <- (carve_obj_range rho k0 (spec_litb_sound k0 (proj1 (forallb_forall _ _) NRO_lit k0 Hk0'))). exact Hz.
    - cbn [app In] in Ho. destruct Ho as [<-|[<-|Ho]].
      + right; left. rewrite RG_ish in Hz. cbn [fst snd] in Hz. lia.
      + left. exists rieS. assert (Hk0' : In rieS NRO) by (unfold NRO; apply in_or_app; right; left; reflexivity). split; [exact Hk0'|].
        rewrite <- (carve_obj_range rho rieS (spec_litb_sound rieS (proj1 (forallb_forall _ _) NRO_lit rieS Hk0'))). exact Hz.
      + unfold N_itmP in Ho. rewrite map_app in Ho. apply in_app_or in Ho as [Ho|Ho].
        * cbn [map In] in Ho. destruct Ho as [<-|[<-|[<-|[<-|[]]]]].
          -- right; right; left. rewrite RG_hdr in Hz. cbn [fst snd] in Hz. lia.
          -- right; right; right; left. rewrite RG_ent in Hz. cbn [fst snd] in Hz. lia.
          -- right; right; right; right; left. rewrite RG_slot in Hz. cbn [fst snd] in Hz. lia.
          -- right; right; right; right; right; left. rewrite RG_stq in Hz. cbn [fst snd] in Hz. lia.
        * destruct vb; cbn [map In] in Ho; [|destruct Ho]. destruct Ho as [<-|[]].
          right; right; right; right; right; right. split; [reflexivity|]. rewrite RG_mag in Hz. cbn [fst snd] in Hz. lia. }

  assert (HNK : forall k0, In k0 NRO -> In (carve_obj k0) R /\ SMGlue.spec_small k0 /\ SMGlue.spec_covered k0
                 /\ cells_in_view rho (rd_of segsA (rm rho)) (fst (SMGlue.spec_range rho k0) - (let '(_, lo, _, _) := k0 in lo)) (let '(_, _, _, cs0) := k0 in cs0)).
  { intros k0 Hk0. assert (CK : carve_okq rho k0).
    { unfold NRO in Hk0. apply in_app_or in Hk0 as [Hk0|[<-|[]]]; [exact (proj1 (Forall_forall _ _) CRTI k0 Hk0) | exact CRIE]. }
    split; [|split; [|split]].
    - unfold R, RQP. unfold NRO in Hk0. apply in_app_or in Hk0 as [Hk0|[<-|[]]]; [apply in_or_app; left; apply in_map; exact Hk0 | apply in_or_app; right; right; left; reflexivity].
    - destruct k0 as [[[b0 lo0] hi0] cs0]. unfold carve_okq in CK. lazy beta iota zeta in CK. destruct CK as (K1 & K2 & K3 & _ & _ & K6 & _).
      unfold SMGlue.spec_small. lazy beta iota zeta. repeat split; assumption.
    - exact (SMGlue.coverb_sound k0 (proj1 (forallb_forall _ _) NRO_chk k0 Hk0)).
    - destruct k0 as [[[b0 lo0] hi0] cs0]. unfold carve_okq in CK. lazy beta iota zeta in CK. destruct CK as (_ & _ & _ & _ & _ & _ & _ & K8).
      cbn [SMGlue.spec_range fst]. lazy beta iota zeta. replace (bv_unsigned (eval rho b0) + lo0 - lo0) with (bv_unsigned (eval rho b0)) by lia. exact K8. }

  assert (INent : In (carved entQ 0 16 [(0, 4%nat, add (SVar 206) (SLit 1)); (4, 4%nat, SVar 207); (8, 8%nat, SVar 201)]) R)
    by (unfold R, RQP; apply in_or_app; right; apply in_or_app; right; unfold N_itmP; cbn [app map In]; right; left; reflexivity).
  assert (INslot : In (carved (add entQ (SAlu ALU_SLL (SVar 206) (SLit 2))) 16 20 [(16, 4%nat, cptrQ vb)]) R)
    by (unfold R, RQP; apply in_or_app; right; apply in_or_app; right; unfold N_itmP; cbn [app map In]; right; right; left; reflexivity).
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPTQ R entQ 0 16 _ Hsm (TQ1_objsP vb) INent ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Eent; lia) ltac:(rewrite Eent; lia)) as [AV1 _].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPTQ R (add entQ (SAlu ALU_SLL (SVar 206) (SLit 2))) 16 20 _ Hsm (TQ1_objsP vb) INslot ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Eslot; lia) ltac:(rewrite Eslot; lia)) as [AV2 _].
  fold rho3 v3 in AV1, AV2. rewrite Eent in AV1. rewrite Eslot in AV2.
  assert (Ek1 : eval rho (add (SVar 206) (SLit 1)) = Z_to_bv 64 (qk + 1)) by (apply ev_add_lit; [cbn [eval]; exact E206 | lia | lia | lia]).
  assert (EBG : bv_unsigned (eval rho (if vb then SVar 210 else vIT)) = qab).
  { destruct vb; [exact E210u|]. rewrite EvIT. specialize (HVBf eq_refl). lia. }
  pose proof (HAU (it_cls it) C1) as AUc. rewrite kUserSpaceSize_val in AUc.
  assert (QD : 0 <= (qab - (qSB + qc * 2 ^ 32)) / 16 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (ECP : eval rho (cptrQ vb) = Z_to_bv 64 ((qab - (qSB + qc * 2 ^ 32)) / 16)).
  { apply bv_eq. rewrite (u64_lit ((qab - (qSB + qc * 2 ^ 32)) / 16)) by lia.
    unfold cptrQ. rewrite U_srl_lit, U_sub, U_sub, U_sll_lit, EBG. unfold vSB. cbn [eval]. rewrite E200, E155, !u64_lit by lia.
    change (32 mod 64) with 32. change (4 mod 64) with 4. unfold M64v. rewrite (Z.mod_small (qc * 2 ^ 32)) by lia.
    rewrite (Z.mod_small (qab - qc * 2 ^ 32)) by lia. rewrite Z.mod_small by lia. change (2 ^ 4) with 16. f_equal. lia. }
  assert (EID : it_id (aa_geom A) it = (qab - (qSB + qc * 2 ^ 32)) / 16)
    by (unfold it_id, it_ab, ptr_to_compact, region_beg, kRegionSize, kCompactPtrScale; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (C_cnt3 : cell_ok v3 (mkACell qE 4 (qk + 1))) by (replace qE with (qE + 0) by lia; exact (av_cell v3 qE 0 4 _ _ rho (fun j => AV1 _ _ _ j (or_introl eq_refl)) Ek1)).
  assert (C_max3 : cell_ok v3 (mkACell (qE + 4) 4 (max_count qc))) by exact (av_cell v3 qE 4 4 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_introl eq_refl))) E207).
  assert (C_sz3 : cell_ok v3 (mkACell (qE + 8) 8 (Size qc))) by exact (av_cell v3 qE 8 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) E201).
  assert (C_slot3 : cell_ok v3 (mkACell (qE + 4 * qk + 16) 4 ((qab - (qSB + qc * 2 ^ 32)) / 16))) by exact (av_cell v3 (qE + 4 * qk) 16 4 _ _ rho (fun j => AV2 _ _ _ j (or_introl eq_refl)) ECP).
  clear AV1 AV2.

  set (CHGo := fun z : Z => (Sh qu <= z < Sh qu + qLEN) \/ (qu - 16 <= z < qu - 8) \/ (qE <= z < qE + 4)
                \/ (qE + 4 * qk + 16 <= z < qE + 4 * qk + 20) \/ (qT + 2768 <= z < qT + 3168) \/ (vb = true /\ qab <= z < qab + 16)).
  assert (VO : forall z, 0 <= z < 2 ^ 64 -> in_ranges rho R (Z_to_bv 64 z) -> ~ CHGo z -> v3 z = v z).
  { intros z Hz Hin NC. pose proof (IRC _ Hin) as RN. rewrite u64_lit in RN by lia. unfold RNG in RN.
    destruct RN as [(k0 & Hk0 & Hr)|[X|[X|[X|[X|[X|X]]]]]]; try (exfalso; apply NC; unfold CHGo; tauto).
    - unfold v3, v. rewrite !view_in by lia.
      exact (SMGlue.absorb_specs_view rho _ tr (vms md tp ms) (vmd md) KEPTQ R NRO (rd_of segsA (rm rho)) Hsm (TQ1_objsP vb) HNK z k0 Hk0 Hr).
    - destruct (Z_lt_dec z (qE + 4)) as [L4|L4]; [exfalso; apply NC; unfold CHGo; right; right; left; lia|].
      destruct (Z_lt_dec z (qE + 8)) as [L8|L8]; [apply (cell_ok_same v v3 _ C_max C_max3); cbn [c_addr c_w]; lia | apply (cell_ok_same v v3 _ C_sz C_sz3); cbn [c_addr c_w]; lia]. }
  assert (PRS : forall z, v z <> None -> v3 z <> None).
  { intros z Hd. destruct (IRdec rho R z) as [[Hz Hin]|NI]; [|unfold v3, rho3; rewrite (proj2 (absorb_io rho R (vms md tp ms)) z NI); exact Hd].
    destruct Hin as (o & Ho & Hr). rewrite u64_lit in Hr by lia.
    destruct (SpineMallocS9.absorb_obj rho _ tr (vms md tp ms) (vmd md) KEPTQ R o Hsm (TQ1_objsP vb) Ho) as (X1 & _ & X3 & _). cbn zeta in X1, X3.
    assert (Do : ob_dflt o = DUnknown).
    { pose proof (proj1 (forallb_forall _ _) (RQP_unk vb) o Ho) as Y. cbv beta in Y. destruct (ob_dflt o); first [reflexivity | discriminate Y | (cbn in Y; discriminate Y)]. }
    unfold obj_range in Hr. cbn [fst snd] in Hr.
    destruct (X3 (or_introl Do) (z - bv_unsigned (eval rho (ob_base o))) ltac:(lia)) as [x Hx].
    unfold v3, rho3. rewrite view_in by lia.
    replace (Z_to_bv 64 z) with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + (z - bv_unsigned (eval rho (ob_base o))))) by (f_equal; lia).
    rewrite Hx. discriminate. }
  set (CHG := fun z : Z => (qab <= z < qu) \/ (Sh qu <= z < Sh qu + qLEN) \/ (qT + 208 <= z < qT + 3168)).
  assert (EQF : forall z, ~ CHG z -> v3 z = v z).
  { intros z NC. destruct (IRdec rho R z) as [[Hz Hin]|NI]; [|exact (proj2 (absorb_io rho R (vms md tp ms)) z NI)].
    apply (VO z Hz Hin). intros HC. apply NC. unfold CHG, CHGo in *. clear - HC K16 C1 EU RZ.
    destruct HC as [X|[X|[X|[X|[X|[_ X]]]]]]; [right; left; exact X | left; lia | right; right; lia | right; right; lia | right; right; lia | left; lia]. }
  assert (NCHG : forall z, ~ (qT <= z < qT + 0x1000) -> (z < 0x7fff8000 \/ 0x10007fff8000 <= z) -> (z < qab \/ qu <= z) -> ~ CHG z).
  { intros z NT NBD NIT HC. unfold CHG in HC. clear - NT NBD NIT HC SH0 SH1 L0. lia. }

  assert (VRO : forall z k0, 0 <= z < 2 ^ 64 -> In k0 NRO -> fst (SMGlue.spec_range rho k0) <= z < snd (SMGlue.spec_range rho k0) -> v3 z = v z).
  { intros z k0 Hz Hk0 Hr. unfold v3, v. rewrite !view_in by lia.
    exact (SMGlue.absorb_specs_view rho _ tr (vms md tp ms) (vmd md) KEPTQ R NRO (rd_of segsA (rm rho)) Hsm (TQ1_objsP vb) HNK z k0 Hk0 Hr). }
  assert (INQW : forall z, (qab <= z < qu) \/ (Sh qu <= z < Sh qu + qLEN) -> QW A z).
  { intros z Hz. left. unfold qzone. rewrite (qall_A1 A HTH), HGL. apply Exists_cons_hd. right. cbn [qb_items]. apply Exists_cons_hd.
    split; [exact QPR|]. unfold it_ab. rewrite L1 in Hz. exact Hz. }
  assert (EQB : forall b, In b (aa_q_global A) -> forall z, qb_addr b <= z < qb_addr b + 8192 -> v3 z = v z).
  { intros b Hb z Hz. apply EQF. apply NCHG.
    - apply HSEP. unfold q_foot. rewrite HTH. cbn [app]. apply Exists_exists. exists b. split; [exact Hb|]. left. unfold kQuarantineBatchSize. exact Hz.
    - right. destruct (batch_addr_facts A HTH rho b BE Hb) as (_ & _ & _ & B4 & _). unfold HIGH_SHADOW_END in B4. lia.
    - assert (Hb' : In b (qall A)) by (rewrite (qall_A1 A HTH); exact Hb).
      assert (IBA : it_ab it + Size (it_cls it) <= qb_addr b \/ qb_addr b + 8192 <= it_ab it) by (eapply item_batch_apart; eassumption).
      unfold it_ab in IBA. clear - IBA Hz UN N8a. lia. }
  assert (NFRESH : ~ In it (its ++ qitems (tmp' ++ rest))).
  { pose proof (HIDS (it_cls it) C1) as ND. apply NoDup_app_r in ND. apply NoDup_app_r in ND. apply NoDup_app_r in ND. unfold q_ids in ND. apply NoDup_app_l in ND.
    rewrite (qall_A1 A HTH), HGL in ND. unfold qitems in ND. cbn [flat_map qb_items app] in ND.
    apply (head_item_fresh _ _ it _ ND). cbv beta. rewrite QPR, Z.eqb_refl. reflexivity. }
  assert (EQI : forall it', In it' (its ++ qitems (tmp' ++ rest)) -> forall z, it_ab it' <= z < fst it' -> v3 z = v z).
  { intros it' Hin' z Hz. assert (NE : it <> it') by (intros X; subst it'; exact (NFRESH Hin')).
    assert (Hin'' : In it' (qitems (qall A))) by (rewrite (qall_A1 A HTH), HGL; unfold qitems; cbn [flat_map qb_items app]; right; exact Hin').
    destruct (qitems_In A it' Hin'') as (b & Hb & Hib). pose proof (rz_facts (snd it')) as (RZ' & _). unfold it_ab in Hz.
    apply EQF. apply NCHG.
    - apply HSEP. unfold q_foot. apply Exists_exists. exists b. split; [exact Hb|]. right. apply Exists_exists. exists it'. split; [exact Hib|]. left. exact Hz.
    - destruct (is_primary (snd it')) eqn:EP.
      + pose proof (item_slot A HQPU HAU HG it' Hin'' EP) as IS'. cbv zeta in IS'. unfold it_ab in IS'.
        destruct IS' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS' & _). unfold HIGH_SHADOW_END in HS'. right. lia.
      + destruct (HSECB it' Hin'' EP) as [X|X]; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in X; [left | right]; lia.
    - destruct (is_primary (snd it')) eqn:EP.
      + assert (IA : it_ab it + Size (it_cls it) <= it_ab it' \/ it_ab it' + Size (it_cls it') <= it_ab it) by (eapply items_apart; eassumption).
        pose proof (item_slot A HQPU HAU HG it' Hin'' EP) as IS'. cbv zeta in IS'. unfold it_ab in IS', IA.
        destruct IS' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UN' & N1' & _). clear - IA Hz UN N8a UN' N1'. lia.
      + destruct (HKSECQ it' Hin'' EP) as [X _]. rewrite kSpaceSize_val in X. clear - X Hz R1 C1 UN N8a TOP. lia. }

  set (A' := push_cache (set_q A [] (mkQB a its s :: tmp' ++ rest)) (it_cls it) (it_id (aa_geom A) it)).
  assert (HK3 : K A' rho3 tp tr md).
  { unfold A'. apply (kq_push_item segsA K HL A rho rho3 tp tr md [] (tmp' ++ rest) a it its s s HTH HGL HCI QPR QNF); [intros i; reflexivity | intros l; reflexivity | | | | | exact HK].
    - intros z NQ NPZ. fold v3 v. destruct (IRdec rho R z) as [[Hz Hin]|NI]; [|exact (proj2 (absorb_io rho R (vms md tp ms)) z NI)].
      apply (VO z Hz Hin). intros HC. unfold CHGo in HC. destruct HC as [X|[X|[X|[X|[X|[_ X]]]]]].
      + apply NQ. apply INQW. right. exact X.
      + apply NQ. apply INQW. left. clear - X RZ. lia.
      + apply NPZ. left. unfold pc_entry. clear - X. lia.
      + apply NPZ. right. unfold pc_entry. clear - X. lia.
      + apply NQ. right. right. unfold qstat_zone. exact X.
      + apply NQ. apply INQW. left. clear - X RZ. lia.
    - intros z _ Hd. exact (PRS z Hd).
    - fold v3. unfold pc_entry. exact C_cnt3.
    - fold v3. unfold pc_entry. rewrite EID. replace (qT + 0xd0 + 80 * qc + 16 + 4 * qk) with (qE + 4 * qk + 16) by lia. exact C_slot3. }

  assert (HCB3 : CURB v3 a n0 (S nd) its).
  { pose proof (CURB_next _ _ _ _ _ _ HCB) as (Q1 & Q2 & Q3 & Q4 & Q5). unfold kQuarantineBatchCount in Q3.
    assert (EQa : forall z, a <= z < a + 8192 -> v3 z = v z) by (intros z Hz; exact (EQB _ INB z Hz)).
    split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply EQa; lia|]. split; [exact Q2|]. split; [exact Q3|].
    split; [eapply present_frame; [|exact Q4]; intros z Hz; apply EQa; unfold kQuarantineBatchSize in Hz; lia|].
    intros j it' Hj. destruct (Q5 j it' Hj) as [Cj Ij]. pose proof (nth_error_In _ _ Hj) as Hin'.
    assert (Hj' : (j < length its)%nat) by (apply (proj1 (nth_error_Some its j)); rewrite Hj; discriminate).
    split.
    - eapply cell_ok_frame1; [|exact Cj]. cbn. intros z Hz. apply EQa. lia.
    - eapply item_mem_frameP; [apply (proj1 (rz_facts (snd it'))) | intros z Hz; exact (EQI it' (in_or_app _ _ _ (or_introl Hin')) z Hz) | exact PRS | exact Ij]. }
  assert (HR3 : RMEM2 v3 (aa_geom A) tmp' rest).
  { destruct HRM as (HBM & HLT & HLR & HTHD & HGH). change Inv.QG with QG in *.
    assert (INQ : forall b, In b (tmp' ++ rest) -> In b (aa_q_global A)) by (intros b Hb; rewrite HGL; right; exact Hb).
    pose proof WINS as W2. unfold hideP in W2. destruct W2 as (WTI & _ & WTB & _ & _ & WTS & _).
    split; [|split; [|split; [|split]]].
    - clear WTI WTB WTS. apply Forall_forall. intros b Hb.
      assert (BP : batch_pure A b) by (apply (proj1 (Forall_forall _ _) (proj1 HQPU) b); rewrite (qall_A1 A HTH); exact (INQ b Hb)).
      apply (batch_mem_frameP A v v3 b BP); [| | exact PRS | exact (proj1 (Forall_forall _ _) HBM b Hb)].
      + intros z Hz. apply (EQB b (INQ b Hb)). lia.
      + intros it' z Hit' Hz. apply (EQI it'); [|exact Hz]. apply in_or_app. right. unfold qitems. apply in_flat_map. exists b. split; [exact Hb | exact Hit'].
    - clear WTI WTB WTS. apply qlinks_to_0. apply (qlinks_to_frame v v3 tmp' 0); [|apply qlinks_to_0; exact HLT].
      intros b z Hb Hz. apply (EQB b (INQ b (in_or_app _ _ _ (or_introl Hb)))). lia.
    - clear WTI WTB WTS. apply qlinks_to_0. apply (qlinks_to_frame v v3 rest 0); [|apply qlinks_to_0; exact HLR].
      intros b z Hb Hz. apply (EQB b (INQ b (in_or_app _ _ _ (or_intror Hb)))). lia.
    - destruct HTHD as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      assert (TOUT : forall z, qT + 0x50 <= z < qT + 0x70 -> v3 z = v z).
      { intros z Hz. apply EQF. unfold CHG. intros [X|[X|X]]; [clear - X Hz WTS R1 C1 UN N8a TOP; lia | clear - X Hz WTB SH0 SH1 L0; lia | clear - X Hz; lia]. }
      clear WTI WTB WTS.
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply TOUT; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply TOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply TOUT; lia].
    - destruct HGH as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      assert (GOUT : forall z, QG + 160 <= z < QG + 192 -> v3 z = v z).
      { intros z Hz. apply EQF. unfold CHG. unfold QG in Hz. intros [X|[X|X]]; [clear - X Hz R1 C1 S2; lia | clear - X Hz SH0; lia | clear - X Hz WTI; lia]. }
      clear WTI WTB WTS.
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply GOUT; lia|].
      split; [intros NE; destruct (Q2 NE) as [Qa Qb]; split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply GOUT; lia|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply GOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply GOUT; lia]. }

  assert (HF3 : FRM A0 rho0 rho3).
  { apply (FRM_absorb_gen A0 rho0 rho rho3 (fun z => 0 <= z < 2 ^ 64 /\ in_ranges rho R (Z_to_bv 64 z)) (IRdec rho R) ltac:(intros i; reflexivity) ltac:(intros l; reflexivity));
      [| | exact (proj2 (absorb_io rho R (vms md tp ms))) | | exact HFRM].
    - intros z [Hz Hin]. pose proof (IRC _ Hin) as RN. rewrite u64_lit in RN by lia. unfold RNG in RN.
      destruct RN as [(k0 & Hk0 & Hr)|[X|[X|[X|[X|[X|[_ X]]]]]]].
      + pose proof (VRO z k0 Hz Hk0 Hr) as EVz. unfold NRO in Hk0. apply in_app_or in Hk0 as [Hk0|[<-|[]]].
        * right. split; [|exact EVz]. right. left. rewrite <- EG. unfold N_rti in Hk0. cbn [In] in Hk0.
          repeat (destruct Hk0 as [<-|Hk0]; [cbn [SMGlue.spec_range fst snd] in Hr; rewrite ?EvC in Hr; cbn [eval] in Hr; rewrite ?u64_lit in Hr by lia; rewrite ?Z.add_0_l in Hr; unfold qrtc_zone; clear - Hr; first [tauto | (repeat right; lia)]|]).
          destruct Hk0.
        * left. right. right. left. exists (it_cls it). split; [exact C1|]. left. unfold rieS in Hr. cbn [SMGlue.spec_range fst snd] in Hr. rewrite Erie in Hr.
          unfold region_info, kRegionInfoStride. rewrite <- EG, kSpaceSize_val. clear - Hr. lia.
      + left. left. apply HQW. apply INQW. right. exact X.
      + left. left. apply HQW. apply INQW. left. clear - X RZ. lia.
      + left. right. left. rewrite <- EG. clear - X C1. lia.
      + left. right. left. rewrite <- EG. clear - X C1 K16. lia.
      + left. left. right. right. unfold qstat_zone. rewrite <- EG. exact X.
      + left. left. apply HQW. apply INQW. left. clear - X RZ. lia.
    - intros x [_ Hin] HBx. rewrite Z_to_bv_bv_unsigned in Hin.
      apply (SpineMallocS9.absorb_defined rho _ tr (vms md tp ms) (vmd md) KEPTQ R x Hsm (TQ1_objsP vb)); [| exact Hin | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in HBx; unfold IMG_HI; clear - HBx; lia].
      apply Forall_forall. intros o Ho. exact (proj1 (forallb_forall _ _) (RQP_wr vb) o Ho).
    - intros x NP. apply (proj1 (absorb_io rho R (vms md tp ms))). intros Hin. apply NP. split; [apply urange|]. rewrite Z_to_bv_bv_unsigned. exact Hin. }

  assert (C_it3 : cell_ok v3 (mkACell (a + 24 + 8 * Z.of_nat nd) 8 (fst it - 16))).
  { unfold HVS in HVs. fold v in HVs. eapply cell_ok_frame1; [|exact HVs]. cbn. intros z Hz. apply (EQB _ INB). cbn [qb_addr]. lia. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (TQ1 vb) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H1) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (TQ1 vb) KEPTQ R tp tr ms md (TQ1_objsP vb) HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU. rewrite TQ2_eq in HU.
  set (J' := JRI K A0 rho0 A' a n0 (S nd) its tmp' rest).
  assert (HU1 : SPA segsA J' (TQ2 vb) rho3 tp (tr, mkCfg ms md)).
  { split; [exact (proj1 HU)|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact HK3|]. split; [exact HCB3|]. split; [exact HR3 | exact HF3]. }
  pose proof (SPA_facts_hold segsA _ rho3 (TQ2 vb) tp _ HU1) as HFa. rewrite (proj1 (TQ3_facts vb)) in HFa. apply Forall_app in HFa as [HFDI _].
  assert (HFpre : Forall (holds rho3) (pre_facts DEPTH_R)) by (unfold F_DI in HFDI; apply Forall_app in HFDI as [X _]; exact X).
  destruct (kq_facts segsA K HL A' rho3 tp _ _ HK3) as [_ HRIG3 HRTC3 _ _ _ _ _ _ _ _ HKTOP3 _].
  assert (HU2 : SPA segsA J' (addo (TQ2 vb) O_sb) rho3 tp (tr, mkCfg ms md)).
  { apply (carve_sb J' (TQ2 vb) rho3 tp _ (aa_geom A') HU1 (proj1 (TQ2_X vb)) (proj1 (TQ3_swf vb)) HRTC3 (proj1 (proj2 (proj2 HRIG3)))).
    rewrite TQ2_objs. exact (OBD_clear_sb A' rho3 cb_cells (ob_cells (SWD vXK vXF vXL vXS)) HKTOP3 HFpre). }
  assert (HU3 : SPA segsA J' (TQ3 vb) rho3 tp (tr, mkCfg ms md)).
  { pose proof HVi as (_ & E163 & _ & _ & _).
    apply (carve_slot_it J' (addo (TQ2 vb) O_sb) rho3 tp _ (a + 152 + 8 * Z.of_nat nd) (fst it - 16) HU2 (proj2 (TQ2_X vb)) (proj2 (TQ3_swf vb))).
    - unfold vS7. cbn [eval]. exact E163.
    - unfold vIT. cbn [eval]. exact E165.
    - lia.
    - lia.
    - replace (a + 152 + 8 * Z.of_nat nd - 128) with (a + 24 + 8 * Z.of_nat nd) by lia. exact C_it3.
    - rewrite TQ2a_objs. pose proof (OBD_fixed A' rho3 cb_cells (ob_cells (SWD vXK vXF vXL vXS)) HKTOP3 HFpre) as FX.
      change (topG (aa_geom A')) with (topG (aa_geom A)) in FX.
      eapply Forall_impl; [|exact FX]. intros o Ho. apply (fixed_clear rho3 (topG (aa_geom A)) o _ _ Ho); lia. }
  assert (HU4 : SPA segsA J' (TQ4 vb) rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact HU3 | exact (TQ4_below vb) |]. intros HF. rewrite (proj2 (TQ3_facts vb)) in HF. exact (proj1 (proj1 (Forall_app _ _ _) HF)). }
  pose proof (JRI_stable K HL A0 rho0 A' a n0 (S nd) its tmp' rest) as HSTI.
  destruct (entM_SPA _ _ RIr MI rho3 tp _ (TQ4_ent vb) HSTI HU4) as (H7 & AG7 & V7 & RM7).
  assert (VV : forall i, In i [160; 161; 162; 163; 164; 165; 166; 184; 185; 186; 187; 208]%positive -> rw (rho_sub rho3 (infer_sub NPRE (ax_S (TQ4 vb)) (ax_S RIr))) i = rw rho i).
  { intros i Hi. rewrite (V7 i (SVar i)); [reflexivity|]. unfold MI, idm. apply in_map_iff. exists i. split; [reflexivity | exact Hi]. }
  eexists. split; [exact H7|].
  destruct HVx as (E184 & E185 & E186 & E187 & E208). destruct HVi as (E162 & E163 & E164 & E165' & E166).
  split; [unfold HVX; rewrite !VV by (cbn; tauto); tauto|]. split; [unfold HVI; rewrite !VV by (cbn; tauto); tauto|].
  unfold HVS. rewrite RM7. exact C_it3.
Qed.
End QIPost.
End SegQ3D_qiq.

(* [comment removed for export] *)
Module SpineMallocS5t.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocE.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section S5T.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := J_alloc_preT AInv W st A Kc (SVar 12).

Lemma JG_pure : forall A Kc rho rhoE tp w (E : axst),
  SPA segs (JG W st A Kc rho) E rhoE tp w -> sep_geom (aa_geom A) /\ prim_room A.
Proof.
  intros A Kc rho rhoE tp w E Hw. split.
  - destruct (proj2 (proj2 Hw)) as (HA & _). exact (sep_geom3_sep _ (proj1 (AInvA_inv3 _ _ _ _ HA))).
  - destruct (proj2 (proj2 Hw)) as (_ & _ & _ & _ & HB & _). exact (budget_ok_alloc_prim _ _ HB).
Qed.

Section TAIL.
Hypothesis SKY : map skel (ss_objs (ax_S (E3p W st tmax))) = map skel ((((sw_s1 :: unwind_objs W ++ A_globals) ++ RT_m1) ++ [O_pcc; O_pcs; O_pck; O_st])).
Hypothesis YX : ax_X (E3p W st tmax) = [].
Hypothesis YF : incl (((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_s1) ++ F_gen) (ss_facts (ax_S (E3p W st tmax))).
Hypothesis YP : In (SPUle (SLit 1) (SVar V_CNT)) (ss_facts (ax_S (E3p W st tmax))).
Hypothesis WY1 : swf (ax_S (Y1 (E3p W st tmax))) = true.
Hypothesis WY2 : swf (ax_S (Y2 (E3p W st tmax))) = true.
Hypothesis WY3 : swf (ax_S (Y3 (E3p W st tmax))) = true.
Hypothesis WY4 : swf (ax_S (Y4 (E3p W st tmax))) = true.
Hypothesis WY5 : swf (ax_S (Y5 (E3p W st tmax))) = true.
Hypothesis WY6 : swf (ax_S (Y6 (E3p W st tmax))) = true.
Hypothesis WY7 : swf (ax_S (Y7 (E3p W st tmax))) = true.
Variable s3 : wsub.
Hypothesis ENT3 : entailsA (Y7 (E3p W st tmax)) (C3 W st tmax) s3 = true.
Hypothesis SID3 : wsub_id_below s3 GW = true.

Lemma e3p_carve : forall A Kc rho tp w rhoX,
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp w ->
  SPA segs (JG W st A Kc rho) (C3 W st tmax) (rho_sub rhoX s3) tp w.
Proof.
  intros A Kc rho tp w rhoX HW HUS HKc Hw.
  apply (b3_carve nW st tmax (E3p W st tmax) SKY YX YF WY1 WY2 WY3 WY4 WY5 WY6 WY7 s3 ENT3 SID3 A Kc rho tp w rhoX HW HUS HKc
           (proj1 (JG_pure A Kc rho rhoX tp w _ Hw))); [|exact Hw].
  exact (cnt_pos_of_fact nW st A Kc rho rhoX tp w _ Hw YP).
Qed.

Lemma e3p_cnt : forall A Kc rho tp w rhoX,
  SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp w -> 1 <= cnt_of A (bv_unsigned (rw rho 12%positive)).
Proof. intros A Kc rho tp w rhoX Hw. exact (cnt_pos_of_fact nW st A Kc rho rhoX tp w _ Hw YP). Qed.

Theorem spine_s3p_tail : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  (1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) -> sep_geom (aa_geom A) -> prim_room A ->
   forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C3 W st tmax) rhoE tp) Q) ->
  forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp) Q.
Proof.
  intros ok A Kc rho tp Q HW HUS HKc HC rhoX.
  apply (triple_pre_pure segs ok _ _ (1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) /\ sep_geom (aa_geom A) /\ prim_room A)).
  { intros w Hw. split; [exact (e3p_cnt A Kc rho tp w rhoX Hw) | exact (JG_pure A Kc rho rhoX tp w _ Hw)]. }
  intros (Hcnt & HSEP & HPRM).
  eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC Hcnt HSEP HPRM (rho_sub rhoX s3))].
  exact (e3p_carve A Kc rho tp w rhoX HW HUS HKc Hw).
Qed.

Theorem espine_s3p_tail : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  (1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) -> sep_geom (aa_geom A) -> prim_room A ->
   forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C3 W st tmax) rhoE tp) Q) ->
  forall rhoX, etriple segs (SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp) Q.
Proof.
  intros A Kc rho tp Q HW HUS HKc HC rhoX.
  apply (etriple_pre_pure segs _ _ (1 <= cnt_of A (bv_unsigned (rw rho 12%positive)) /\ sep_geom (aa_geom A) /\ prim_room A)).
  { intros w Hw. split; [exact (e3p_cnt A Kc rho tp w rhoX Hw) | exact (JG_pure A Kc rho rhoX tp w _ Hw)]. }
  intros (Hcnt & HSEP & HPRM).
  eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC Hcnt HSEP HPRM (rho_sub rhoX s3))].
  exact (e3p_carve A Kc rho tp w rhoX HW HUS HKc Hw).
Qed.
End TAIL.

Section CERT.
Hypothesis Cert3p : check_cfgA segsA 4000%nat [0x40cc4; 0x3c480] GW [C2p W st tmax] [E3p W st tmax] = true.
Theorem spine_s3p_cert : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (J W st A Kc) ->
  (forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (C2p W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x40cc4; 0x3c480] GW [C2p W st tmax] [E3p W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact Cert3p.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply (HC rhoX)].
  - left. reflexivity.
Qed.
End CERT.

Section ECERT.
Hypothesis NXC2p : (GW <= ss_next (ax_S (C2p W st tmax)))%positive.
Hypothesis ECert3p : check_ecfgA segsA 4000%nat [0x40cc4; 0x3c480] GW [mkVNA (C2p W st tmax) 1 (SLit 0)] [mkVNA (E3p W st tmax) 0 (SLit 0)] = true.
Theorem espine_s3p_cert : forall (A : AA) (Kc : KcA) rho tp (Q : world -> Prop),
  stopJ_stable W st -> Kc_ok Kc ->
  (forall rhoX, etriple segs (SPA segs (JG W st A Kc rho) (E3p W st tmax) rhoX tp) Q) ->
  forall rhoE, etriple segs (SPA segs (JG W st A Kc rho) (C2p W st tmax) rhoE tp) Q.
Proof.
  intros A Kc rho tp Q HUS HKc HC rhoE.
  apply (ecfg_cut 4000%nat [0x40cc4; 0x3c480] GW [mkVNA (C2p W st tmax) 1 (SLit 0)] [mkVNA (E3p W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C2p W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC2p].
  - exact ECert3p.
  - intros E rhoX HinE. clear NXC2p ECert3p. destruct HinE as [<-|[]]; cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply (HC rhoX)].
  - left. reflexivity.
Qed.
End ECERT.
End S5T.
End SpineMallocS5t.

(* [comment removed for export] *)
Module SpineMallocEc.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "app"; "list"; "nil"; "prod"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "swf"; "sobj"; "ss_next"; "ss_facts"; "SVar"; "valuation"; "SLit"; "SPBranch"; "sprop_below"; "ss_objs"; "SPNot"; "rm"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E2a"; "E2b"; "C1g"; "F_gen"; "C2p0"; "C2r0"; "creg_a"; "creg_b"; "F_cls"; "V_CLS"; "V_ND"; "C2p"; "C2r"; "F_pop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "E2a'"; "E2b'"; "only_var"; "tab_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "X2"; "X2r"; "skel"; "X1"; "X1b"; "X1c"; "X1r"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "ulink"; "unwind_factsS"; "unwind_objs"; "J_alloc_preT"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocE.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section EC.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S2fS5eVCST;R1A2S5eS68R2A2S1F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S58VAInv;VW;Vst;VA;VKc;S16PcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S5dS17SaS63Q40A1A1S67VAInv;R4R3R2R1A4S5fS61Vsegs;S1dR4A1A2S60Z182f1cU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Section E_spine_s2C.
Let Xa : axst := ltac2:(tb__ "0|0|
S5S1fVW;Vst;Vtmax;A3S2S37VnW;Vst;Vtmax;A3A1A2").
Let Xb : axst := ltac2:(tb__ "0|0|
S5S20VW;Vst;Vtmax;A3S2S38VnW;Vst;Vtmax;A3A1A2").
Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0S6S35S2eUfa0S8S2fZ40bacSbS2fA1A3S2dS8S3S21VW;Vst;Vtmax;A3SbS3A1M0A3S8S3S1fVW;Vst;Vtmax;A3S8S3S20VW;Vst;Vtmax;A3G0A3A3A6S7A3").
Hypothesis OVa : ltac2:(tb__ "0|0|
S0S6S39P9dS25VW;Vst;Vtmax;A3A2S7A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0S6S39P9dS26VW;Vst;Vtmax;A3A2S7A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0S6S3aP9dS25VW;Vst;Vtmax;A3S51Z208S65S66S48S49S4aS48S4bA1A1A1A1A1A1A5S7A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0S6S3aP9dS26VW;Vst;Vtmax;A3S51Z18U3eA5S7A3").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0S6S12S2S37VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0S6S12S2S38VnW;Vst;Vtmax;A3A1A1S7A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0SfScSaScS11S11A2M0A1M1SaS10A1M2A2M3A1S4dS2S1fVW;Vst;Vtmax;A3A1S2S37VnW;Vst;Vtmax;A3A1A2SeG3SdG1G2S8G0SdS11S11S25VW;Vst;Vtmax;A3S16S28A1A4SbG0A1A3SbS10A1A4A2A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0SfScSaScS11S11A2M0A1M1SaS10A1M2A2M3A1S4dS2S20VW;Vst;Vtmax;A3A1S2S38VnW;Vst;Vtmax;A3A1A2SeG3SdG1G2S8G0SdS11S11S26VW;Vst;Vtmax;A3S16S28A1A4SbG0A1A3SbS10A1A4A2A3").
Hypothesis NXa : ltac2:(tb__ "0|0|
S0S30S14S2S37VnW;Vst;Vtmax;A3A1A1S14S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S30S14S2S38VnW;Vst;Vtmax;A3A1A1S14S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fa : ltac2:(tb__ "0|0|
S43S10S19S4cS18Z200A1S16S29A1A3S15S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S43S10S1cS19S4cS18Z200A1S16S29A1A3A1S15S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Ga : ltac2:(tb__ "0|0|
S42S10S22S15S2S1fVW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S42S10S22S15S2S20VW;Vst;Vtmax;A3A1A1A3").
Hypothesis SKa : ltac2:(tb__ "0|1|
S0SaScScS11S11A2S11A2M0A1S31S13G0S3dS1bS2VXa;A1A1A4S31S13G0S3dS9S13S8S13S50S9S13S57VW;A1S52A3A3S4fA3A4A3").
Hypothesis SKb : ltac2:(tb__ "0|1|
S0SaScScS11S11A2S11A2M0A1S31S13G0S3dS1bS2VXb;A1A1A4S31S13G0S3dS9S13S8S13S50S9S13S57VW;A1S52A3A3S4fA3A4A3").
Hypothesis XXa : ax_X Xa = [].
Hypothesis XXb : ax_X Xb = [].
Hypothesis XFa : ltac2:(tb__ "0|0|
S42S10S9S10S9S10S9S10S56VW;Vst;A2S54S53A1A3S4eA3S22A3S15S2VXa;A1A1A3").
Hypothesis XFb : ltac2:(tb__ "0|0|
S42S10S9S10S9S10S9S10S56VW;Vst;A2S54S53A1A3S4eA3S22A3S15S2VXb;A1A1A3").
Hypothesis W1a : ltac2:(tb__ "0|0|
S0S6S12S2S3eVXa;A1A1A1S7A3").
Hypothesis W1ba : ltac2:(tb__ "0|0|
S0S6S12S2S3fVXa;A1A1A1S7A3").
Hypothesis W1ca : ltac2:(tb__ "0|0|
S0S6S12S2S40VXa;A1A1A1S7A3").
Hypothesis W2a : ltac2:(tb__ "0|0|
S0S6S12S2S3bVXa;A1A1A1S7A3").
Hypothesis W1ra : ltac2:(tb__ "0|0|
S0S6S12S2S41VXa;A1A1A1S7A3").
Hypothesis W2ra : ltac2:(tb__ "0|0|
S0S6S12S2S3cVXa;A1A1A1S7A3").
Hypothesis W1b : ltac2:(tb__ "0|0|
S0S6S12S2S3eVXb;A1A1A1S7A3").
Hypothesis W1bb : ltac2:(tb__ "0|0|
S0S6S12S2S3fVXb;A1A1A1S7A3").
Hypothesis W1cb : ltac2:(tb__ "0|0|
S0S6S12S2S40VXb;A1A1A1S7A3").
Hypothesis W2b : ltac2:(tb__ "0|0|
S0S6S12S2S3bVXb;A1A1A1S7A3").
Hypothesis W1rb : ltac2:(tb__ "0|0|
S0S6S12S2S41VXb;A1A1A1S7A3").
Hypothesis W2rb : ltac2:(tb__ "0|0|
S0S6S12S2S3cVXb;A1A1A1S7A3").
Variables sa sra sb srb : wsub.
Hypothesis ENTa : ltac2:(tb__ "0|0|
S0S6S4S3bVXa;A1S23VW;Vst;Vtmax;A3Vsa;A3S7A3").
Hypothesis ENTra : ltac2:(tb__ "0|0|
S0S6S4S3cVXa;A1S24VW;Vst;Vtmax;A3Vsra;A3S7A3").
Hypothesis ENTb : ltac2:(tb__ "0|0|
S0S6S4S3bVXb;A1S23VW;Vst;Vtmax;A3Vsb;A3S7A3").
Hypothesis ENTrb : ltac2:(tb__ "0|0|
S0S6S4S3cVXb;A1S24VW;Vst;Vtmax;A3Vsrb;A3S7A3").
Hypothesis SIDa : ltac2:(tb__ "0|0|
S0S6S32Vsa;S2dA2S7A3").
Hypothesis SIDra : ltac2:(tb__ "0|0|
S0S6S32Vsra;S2dA2S7A3").
Hypothesis SIDb : ltac2:(tb__ "0|0|
S0S6S32Vsb;S2dA2S7A3").
Hypothesis SIDrb : ltac2:(tb__ "0|0|
S0S6S32Vsrb;S2dA2S7A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S6S44S10S1aS14S2S23VW;Vst;Vtmax;A3A1A1A1S9S10S27S2cA3A3S7A3").
Hypothesis FBr : ltac2:(tb__ "0|0|
S0S6S44S10S1aS14S2S24VW;Vst;Vtmax;A3A1A1A1S27A3S7A3").

Hypothesis NXC1g : ltac2:(tb__ "0|0|
S6bS2dS14S2S21VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECert2 : ltac2:(tb__ "0|3|
S0S6S36S2eUfa0S8S2fZ40bacSbS2fA1A3S2dS8S33S34S21VW;Vst;Vtmax;A3Z1S18Z0M0A1M1A3SbS33A1M2A3S8S33S34S1fVW;Vst;Vtmax;A3G0G1A3S8S33S34S20VW;Vst;Vtmax;A3G0G1A3G2A3A3A6S7A3").
Theorem espine_s2c : ltac2:(tb__ "0|2|
S5dS59S17SaS63Q40M0A1A1S46OF_;S0S5cVst;S5bA3S0SaS55A1VW;SbS55A1A3F_;S6aVW;Vst;A2S5aR6A1S17S45Vsegs;S47Vsegs;S62VW;Vst;R9R8R7A5S2aVW;Vst;Vtmax;A3R1R6A5R5A3FrhoE;S0S2fS69R9S64G0S1eR7PcA2A2A2Z0A3S17S45Vsegs;S47Vsegs;S62VW;Vst;RbRaR9A5M1S2bVW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;S17S45Vsegs;S47Vsegs;G1S21VW;Vst;Vtmax;A3R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Q HW HUS HKc HP HR rhoE.
  pose proof (Zle_0_nat (length (cs_cache (cst_of A (bv_unsigned (rw rho 12%positive)))))) as Hc0.
  change (0 <= cnt_of A (bv_unsigned (rw rho 12%positive))) in Hc0.
  apply (ecfg_cut 4000%nat [0x40bac] GW [mkVNA (C1g W st tmax) 1 (SLit 0)] [mkVNA (E2a W st tmax) 0 (SLit 0); mkVNA (E2b W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (C1g W st tmax) _ (JG_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. destruct Hn as [<-|[]]; cbn [vna_state]; first [exact NXC1g].
  - exact ECert2.
  - intros E rhoX HinE. clear NXC1g ECert2. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sa))].
        apply (b1_pop nW st tmax Xa SKa XXa XFa W1a W1ba W1ca W2a sa sra ENTa SIDa FB ENTra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX sra))].
        apply (b1_refill nW st tmax Xa SKa XXa XFa W1ra W2ra sa sra ENTa FB ENTra SIDra FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_a nW st tmax OVa TABa Wa' Da' NXa NXb Fa Ga A Kc rho tp w rhoX Hw).
    +
      destruct (Z_lt_dec 0 (cnt_of A (bv_unsigned (rw rho 12%positive)))) as [Hp|Hz].
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HP (rho_sub rhoX sb))].
        apply (b1_pop nW st tmax Xb SKb XXb XFb W1b W1bb W1cb W2b sb srb ENTb SIDb FB ENTrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
      * eapply etriple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HR ltac:(clear -Hz Hc0; lia) (rho_sub rhoX srb))].
        apply (b1_refill nW st tmax Xb SKb XXb XFb W1rb W2rb sb srb ENTb FB ENTrb SIDrb FBr A Kc rho tp w rhoX HW HUS HKc ltac:(lia)).
        exact (class_restate_b nW st tmax OVb TABb Wb' NXa NXb Db' Fb Gb A Kc rho tp w rhoX Hw).
  - left. reflexivity.
Qed.
End E_spine_s2C.
End EC.
End SpineMallocEc.

