(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From Stdlib Require NArith PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.

(* [comment removed for export] *)
Module CertMallocSR.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "app"; "prod"; "false"; "option"; "true"; "list"; "bool"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sv"; "cell"; "sobj"; "mkCell"; "SAlu"; "SVar"; "SPUle"; "mkObj"; "DUnknown"; "ss_objs"; "SPAlign"; "ss_facts"; "SPBranch"; "DZero"; "SMd"; "SPNot"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "SPUlt"; "ss_next"; "ss_pc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_LTU"; "M_MUL"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "leafA"; "cell_eqb"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vK"; "F_pop"; "pcof"; "updR"; "vMU"; "nxt"; "rst"; "addobjs"; "vNEW"; "vAU"; "vNF"; "F_new"; "O_cell"; "nobj"; "vCHX"; "vMC"; "vMFA"; "F_r0"; "F_r1"; "LNX"; "LV3"; "PV4"; "PV6"; "beg1"; "beg2"; "choffK"; "keepn"; "sMS"; "vRI"; "F_x"; "GR"; "HINT_au"; "HINT_k"; "HINT_map"; "LV0"; "LV2"; "O_pccK"; "O_pckK"; "O_pcm"; "O_ri"; "PNX"; "PNX1"; "PV5"; "PV7"; "cE3a"; "cE3b"; "cR0a"; "idx_rot"; "rMS"; "req_e"; "ri_cells"; "rotM"; "selobjs"; "setobj"; "sh1"; "sh2"; "tMS"; "vFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_SIZE"; "pc_base"; "V_CLS"; "O_pcs"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@Corelib.Lists.ListDef"; "firstn"; "seq"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "vSB"; "vRIS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "gsv"; "shb"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA EntailA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP.
Import ListNotations.
Open Scope Z_scope.

Definition GR : positive := 240%positive.
Definition vMC : sv := SVar 220.  Definition vNF : sv := SVar 221.  Definition vMFA : sv := SVar 222.  Definition vAU : sv := SVar 223.
Definition vMU : sv := SVar 224.  Definition vRI : sv := SVar 225.  Definition vFA : sv := SVar 226.   Definition vK : sv := SVar 227.
Definition vNEW : sv := SVar 228.

Definition O_pcm : sobj := ltac2:(tb__ "0|2|
S15S6dScZ4M0A1M1ScZ8A1S0SfS11G1G0S41A3S1SfA1A3S16A5").
Definition O_pch : sobj := ltac2:(tb__ "0|0|
S15S6dScZ10A1ScZ50A1S1SfA1S16A5").

Definition ri_cells : list cell := ltac2:(tb__ "0|2|
S0SfS11ScZ0A1M0Z8M1G0A3S0SfS11ScZ10A1G1S3cA3S0SfS11ScZ18A1G1S42A3S0SfS11ScZ20A1G1S3bA3S0SfS11ScZ28A1G1G0A3S0SfS11ScZ30A1G1S36A3S0SfS11ScZ38A1G1G0A3S0SfS11ScZ44A1Z1G0A3S1SfA1A3A3A3A3A3A3A3A3").
Definition O_ri : sobj := ltac2:(tb__ "0|0|
S15S4eScZ0A1ScZ80A1S64S16A5").

Definition ri_e : sv := ltac2:(tb__ "0|0|
S12S28S7bS12S29S13S6eA1ScZ7A1A3A3").
Definition rb_e : sv := ltac2:(tb__ "0|0|
S12S28S7aS12S29S13S6eA1ScZ20A1A3A3").
Definition fa_e : sv := ltac2:(tb__ "0|0|
S12S28S7aS12S28S12S29S13S6eA1ScZ20A1A3ScZe0000000A1A3A3").
Definition k_e : sv := SAluW ALU_SRL vMC (SLit 1).

Definition F_r0 : list sprop := ltac2:(tb__ "0|0|
S0SdS14ScZ2A1S41A2S0SdS14S41ScZ10A1A2S1SdA1A3A3").
Definition F_r1 : list sprop := ltac2:(tb__ "0|0|
S0SdS18Pe1Z7A2S0SdS18Pe2ZcA2S0SdS14ScZ1A1S32A2S0SdS14S32ScZ8A1A2S0SdS14S3cScZ8000000A1A2S0SdS14S3bS36A2S0SdS18Pe0Z12A2S0SdS18P9bZ10A2S1SdA1A3A3A3A3A3A3A3A3").
Definition req_e : sv := SAlu ALU_SUB vK vNF.

Definition HINT_map : sprop := ltac2:(tb__ "0|0|
S1aS2aS36S12S28S3bS1cS2bS13S6cA1S63A3A3A3").

Definition runC (cutpcs : list Z) (C : axst) : list leafA := ltac2:(tb__ "0|1|
S7S9S2fA1M0A1G0Lx;S31S7fUfa0Vcutpcs;VC;S8A5G0R1Ll;S1S2fA1X7x2").

Definition updR (FR : list sprop) (E : axst) (pc : Z) (ru : list (nat * sv)) (objs : list sobj) (reset : bool) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
S2dVE;A1S24S2eVE;S1eVpc;S81S22R1A1Vru;A2S20R1A1S1fR1A1S23R1A1S4S10S17R1A1Vobjs;A3S4SdSaS9SdA1Lreset;Vreset;VFR;S19R1A1Xax2Vfacts;A3Vnx;S21R1A1A9A2TS;").
Definition nxt (E : axst) : positive := ss_next (ax_S E).
Definition pcof (E : axst) : Z := ss_pc (ax_S E).

Definition rst (FR : list sprop) (E : axst) (ru : list (nat * sv)) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S35VFR;VE;S34VE;A1Vru;S1S10A1S8Vfacts;S37VE;A1A8").

Definition addobjs (E : axst) (objs : list sobj) (nx : positive) : axst := ltac2:(tb__ "0|0|
S2dVE;A1S24S2eVE;S1eS27R1A1S22R1A1S20R1A1S1fR1A1S23R1A1S4S10S17R1A1Vobjs;A3S19R1A1Vnx;S21R1A1A9A2TS;").

Definition keepn (E : axst) (n : nat) : axst := ltac2:(tb__ "0|1|
S2eVE;S74S2dVE;A1M0S75S10Vn;S17G0A1A3A2A2").

Definition setobj (E : axst) (i : nat) (o : sobj) : axst := ltac2:(tb__ "0|2|
S2eVE;S74S2dVE;A1M0S4S10S75S10Vi;S17G0A1M1A3S0S10Vo;S77S10SbVi;A1G1A3A3A3A2A2").

Definition selobjs (E : axst) (idxs : list nat) : axst := ltac2:(tb__ "0|1|
S2eVE;S74S2dVE;A1M0S83S17G0A1Vidxs;A2A2A2").

Definition factsR (E3 : axst) : list sprop := ltac2:(tb__ "0|0|
S4SdS19S2dVE3;A1A1S4SdS43S44A3A3").

Definition F_pop : list sprop := ltac2:(tb__ "0|0|
S0SdS1aS2aS3cS32A3S0SdS53S0SdS14S36ScZdffc0000A1A2S1SdA1A3A3A3").
Definition F_new : list sprop := ltac2:(tb__ "0|0|
S0SdS14ScZ4A1S3aA2S0SdS14S3aScZ2001A1A2S0SdS14S42ScZ1ffc0000A1A2S0SdS18PdeZ12A2S1SdA1A3A3A3A3").

Definition HINT_au : sprop := ltac2:(tb__ "0|0|
S1dS1aS2aS12S28S36ScZ40000A1A3S12S28S3bS1cS2bS3aS13S6cA1A3A3A3A1").
Definition HINT_k : sprop := ltac2:(tb__ "0|0|
S1dS1aS2aS12S28S3cS3aA3S32A3A1").

Definition beg1 : sv := SAlu ALU_ADD vMU rb_e.
Definition O_up : sobj := ltac2:(tb__ "0|0|
S15S49ScZ0A1ScZ40000A1S1SfA1S1bA5").
Definition sh1 : sv := ltac2:(tb__ "0|0|
S12S28S7cS49A1S7dA3").
Definition O_sh1 : sobj := ltac2:(tb__ "0|0|
S15S68ScZ0A1ScZ8000A1S1SfA1S16A5").
Definition fa_e2 : sv := SAlu ALU_ADD rb_e (SLit 3758096384).
Definition beg2 : sv := SAlu ALU_ADD vMFA fa_e2.
Definition O_fp : sobj := ltac2:(tb__ "0|0|
S15S4aScZ0A1ScZ40000A1S1SfA1S1bA5").
Definition sh2 : sv := ltac2:(tb__ "0|0|
S12S28S7cS4aA1S7dA3").
Definition O_sh2 : sobj := ltac2:(tb__ "0|0|
S15S69ScZ0A1ScZ8000A1S1SfA1S16A5").

Definition cR0a (E3 : axst) : axst := ltac2:(tb__ "0|0|
S39VE3;S0S10S58S0S10S59S1S10A1A3A3S50A3").
Definition cR0 (E3 : axst) : axst := ltac2:(tb__ "0|0|
S79S60VE3;A1S4SdS19S2dVE3;A1A1S4SdS43S44A3A3A2").
Definition cR1 (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU8S4eA4S0G0S3S2SeU14S6bA4S0G0S3S2SeUeS32A4S1G0A1A3A3A3S1SdA1A4").

Definition cPa (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU15S13S6cA1A4S1G0A1A3S33A4").
Definition cPb (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU15S13S6cA1A4S1G0A1A3S33A4").
Definition cP2 (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU13ScZ40000A1A4S0G0S3S2SeU14S36A4S1G0A1A3A3S33A4").

Definition cP2c (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S35VFR;VE;S34VE;A1S0S5S2SeA2M0S3S2SeU13ScZ40000A1A4S0G0S3S2SeU14S36A4S0G0S3S2SeUbS13Pf1A1A4S0G0S3S2SeUfS13Pf5A1A4S0G0S3S2SeU10S13Pf6A1A4S1G0A1A3A3A3A3A3S1S10A1S8S33PfaA8").
Definition cX (E : axst) (eb : sv) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeUaVeb;A4S1G1A1A3S1S10A1S6G0S37VE;A1A8").
Definition gX (C : axst) (eb : sv) (o : sobj) : axst := ltac2:(tb__ "0|1|
S2eVC;S82S2dVC;A1M0Veb;S4S10S17G0A1S0S10Vo;S1S10A1A3A3S26G0A1A4A2").
Definition cM (E : axst) (osh : sobj) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeUcScZ8000A1A4S1G1A1A3S0S10Vosh;S1S10A1A3S6G0S37VE;A1A8").

Definition sMS (C : axst) : wsub := ltac2:(tb__ "0|0|
S78P1S2dVC;A1S2dS72A1A3").
Definition rMS (C : axst) : list sobj := ltac2:(tb__ "0|1|
S7S9S10A1M0A1G0Lx;S85VC;S72S4dVC;A1A3G0R1LR;S1S10A1X7x2").
Definition tMS (C : axst) : axst := ltac2:(tb__ "0|0|
S86S4dVC;A1S72S80S87S73A1A1VC;S62VC;A1A5").
Definition dMS (C : axst) : axst := ltac2:(tb__ "0|0|
S79S6aVC;A1S19S2dVC;A1A1A2").

Definition nobj (E : axst) : nat := length (ss_objs (ax_S E)).
Definition idx_rot (E : axst) : list nat := ltac2:(tb__ "0|1|
S4S2S76U1M0S70S3fVE;A1G0A2A2S0S2U0S1S2A1A3A3").
Definition rotM (E : axst) : axst := ltac2:(tb__ "0|0|
S66VE;S61VE;A1A2").
Definition relM (E : axst) : axst := ltac2:(tb__ "0|0|
S4cS65VE;A1S70S3fVE;A1U2A2A2").
Definition cD (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU13S3aA4S1G0A1A3S4SdS33S3dA3A4").
Definition cFm (E : axst) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeU8S12S28S42ScZ40000A1A3A4S1G1A1A3S1S10A1S6G0S37VE;A1A8").

Definition LV0 : positive := 400%positive. Definition LV2 : positive := 402%positive. Definition LV3 : positive := 403%positive.
Definition LNX : positive := 410%positive.
Definition O_cell (v : positive) (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S15S13Vv;A1ScZ0A1ScZ4A1Vcs;S16A5").
Definition cL0 (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|2|
S35VFR;VE;S34VE;A1S0S5S2SeA2M0S3S2SeUaS13S54A1A4S0G0S3S2SeUcS13S55A1M1A4S0G0S3S2SeUeS12S2cG1ScZ4A1A3A4S0G0S3S2SeUfS13S46A1A4S1G0A1A3A3A3A3S1S10A1S8S4SdS33S3dA3S45A8").
Definition cL1 (C : axst) : axst := ltac2:(tb__ "0|0|
S39VC;S0S10S3eS46S1SfA1A2S1S10A1A3S45A3").
Definition cXL (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|0|
S38VFR;VE;S1S5S2SeA2A1S4SdS33S4SdS3dS0SdS51S0SdS52S1SdA1A3A3A3A3A4").

Definition PV4 : positive := 524%positive. Definition PV5 : positive := 525%positive. Definition PV6 : positive := 526%positive.
Definition PV7 : positive := 527%positive. Definition PNX : positive := 527%positive. Definition PNX1 : positive := 528%positive.
Definition cT0 (E : axst) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeUdS13S47A1A4S0G1S3S2SeU14S13S48A1A4S0G1S3S2SeUcS13S5cA1A4S1G1A1A3A3A3S1S10A1S6G0S5aA8").
Definition cT1 (C : axst) : axst := ltac2:(tb__ "0|1|
S39VC;S0S10S3eS48S0SfS11ScZ0A1Z4S13S5dA1A3S1SfA1M0A3A2S0S10S3eS47G0A2S1S10A1A3A3S5bA3").

Definition vCHX : sv := SVar 229.
Definition choffK : sv := ltac2:(tb__ "0|0|
S12S28S12S29S12S28S32ScN1A1A3ScZ2A1A3ScZ10A1A3").
Definition O_pccK : sobj := ltac2:(tb__ "0|2|
S15S6dScZ0A1M0ScZ4M1A1S0SfS11G0G1S32A3S1SfA1A3S16A5").
Definition O_pckK : sobj := ltac2:(tb__ "0|0|
S15S6dS4bScZ50A1S0SfS11S4bZ4S40A3S1SfA1A3S16A5").
Definition F_x : list sprop := ltac2:(tb__ "0|0|
S0SdS25S40ScS8aZ2Z1cA2A1A2S1SdA1A3").
Definition s_exit (E Ep : axst) : wsub := ltac2:(tb__ "0|1|
S0S5S71SeA2M0S3S71SeP95S32A4S0G0S3S71SeP9fS40A4S78S7eS2dVE;A1S2dVEp;A1A3A3A3").

Definition cE1 (E : axst) (ic : nat) : axst := ltac2:(tb__ "0|0|
S67VE;Vic;S56A3").
Definition cE2 (E : axst) : axst := ltac2:(tb__ "0|0|
S4cVE;S70S3fVE;A1U2A2A2").
Definition cE3a (E : axst) : axst := ltac2:(tb__ "0|0|
S39VE;S0S10S6fS1S10A1A3S37VE;A1A3").
Definition cE3b (E : axst) : axst := ltac2:(tb__ "0|0|
S39S5eVE;A1S0S10S57S1S10A1A3S37VE;A1A3").
Definition cE3 (E : axst) : axst := ltac2:(tb__ "0|0|
S84S4fS5fVE;A1A2").

Definition ri_has (cells : list cell) (e16 e24 e32 e48 : sv) : bool := ltac2:(tb__ "0|2|
S89SfSfS88SfS30R1A1Vcells;A3Lcc;S0SfS11ScZ0A1M0Z8M1G0A3S0SfS11ScZ10A1G1Ve16;A3S0SfS11ScZ18A1G1Ve24;A3S0SfS11ScZ20A1G1Ve32;A3S0SfS11ScZ28A1G1G0A3S0SfS11ScZ30A1G1Ve48;A3S0SfS11ScZ38A1G1G0A3S0SfS11ScZ44A1Z1G0A3S1SfA1A3A3A3A3A3A3A3A3A3").
End CertMallocSR.

(* [comment removed for export] *)
Module InvKf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_fs_busy"; "aa_fs_hint"; "aa_geom"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "mkAA"; "DG"; "aa_depot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.InvKf"; "bumpKf"; "@Corelib.Init.Datatypes"; "list"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "with_depot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition bumpKf (A : AA) : AA := ltac2:(tb__ "0|0|
SfS8VA;A1S5VA;A1S4VA;A1SeVA;A1SbVA;A1SaVA;A1SdVA;A1ScVA;A1S11VA;A1S7VA;A1S6VA;A1S9VA;A1S3VA;A1S2VA;A1S1aS1VA;A1Z1A2Af").

Lemma AInvX_bumpKf : ltac2:(tb__ "0|0|
S0S15S13S1bQ40A1A1S14S17R4R3R2R1A4S17S12R5A1R4R3R2A4F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB).
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [|exact (conj HI3 HB)].
  unfold model_inv_nd, ledger_inv_nd, gap_ok, gapN_ok, gapS_ok, blocks_left, budget_boundD in HM |- *.
  rewrite (PrimCredit.prim_credit_same A (bumpKf A) eq_refl).
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec bumpKf] in HM |- *.
  destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & _ & L6 & L7 & L8 & L9).
  split; [exact V1|]. split; [unfold BETA1 in *; set (pc := PrimCredit.prim_credit A) in *; clearbody pc; clear -V2 V6; lia|]. split; [exact V3|]. split; [exact V4|]. split; [exact V5|].
  split; [clear -V6; lia|]. split; [exact V7|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact I|].
  split; [exact I|]. split; [exact L7|].
  split; [exact L8|exact L9].
Qed.

Theorem AInvA_bumpKf : ltac2:(tb__ "0|0|
S0S15S13S1bQ40A1A1S14S16S19R4R3R2R1A5S16S19S12R5A1R4R3R2A5F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA. destruct (AInvA_X A rho tp md HA) as (HX & HD & L6).
  apply X_AInvA; [exact (AInvX_bumpKf A rho tp md HX) | exact HD | cbn [aa_depot aa_Km aa_Kf bumpKf]; lia].
Qed.

Lemma bumpKf_with_depot : ltac2:(tb__ "0|0|
S0S10S1cS0S12S18R2R1A2A1SfS8R2A1S5R2A1S4R2A1SeR2A1SbR2A1SaR2A1SdR2A1ScR2A1R1S7R2A1S6R2A1S9R2A1S3R2A1S2R2A1S1aS1R2A1Z1A2AfA3FG;FA;").
Proof. reflexivity. Qed.
End InvKf.

(* [comment removed for export] *)
Module SegQI_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "nat"; "true"; "pair"; "prod"; "false"; "list"; "app"; "None"; "Some"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "sobj"; "SAlu"; "SVar"; "ss_next"; "ss_lenient"; "SPUle"; "cell"; "ss_facts"; "SPBranch"; "SPAlign"; "mkCell"; "DUnknown"; "mkObj"; "SExt"; "SPNot"; "mkSS"; "sprop_below"; "sprop_eqb"; "SPUlt"; "FcsrFrm0"; "SMd"; "ss_fcsr"; "ss_fregs"; "ss_objs"; "ss_regs"; "ss_resv"; "sstate"; "SMdW"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "axwf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "add"; "leaf"; "NPRE"; "vSB"; "vMX"; "vPK"; "vST"; "DEPTH_Q"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states"; "vCLS"; "updQ"; "vSZ"; "NXI"; "QI1"; "C5a"; "C5b"; "MSENTQ"; "PSENT"; "QCENTI"; "QI0"; "QI2"; "QI3"; "vN8"; "C1a"; "C1b"; "E1ba"; "E1bb"; "PreQI"; "bgv"; "s5a"; "s5b"; "C0a"; "C0b"; "C2a"; "C2b"; "C3a"; "C3b"; "C4a"; "C4b"; "C6a"; "C6b"; "E1aa"; "E1ab"; "F_QI"; "LENq"; "R5a"; "R5b"; "XF"; "run1a"; "run1b"; "E0a"; "E0b"; "E2a"; "E2b"; "E3a"; "E3b"; "E4a"; "E4b"; "E5a"; "E5b"; "E6a"; "E6b"; "QIRET"; "T5a"; "T5b"; "T5fa"; "T5fb"; "dI0"; "dI1a"; "dI1b"; "dI2"; "dI3"; "dI4"; "dI5"; "dI6"; "run0a"; "run0b"; "run2a"; "run2b"; "run3a"; "run3b"; "run4a"; "run4b"; "run5a"; "run5b"; "run6a"; "run6b"; "run7a"; "run7b"; "vAB"; "vHW"; "E1aa'"; "E1ab'"; "E1ba'"; "E1bb'"; "E7a"; "E7b"; "O_cb"; "O_entI"; "O_hdrI"; "O_ish"; "O_rie"; "O_slotI"; "O_stq"; "PostQI"; "RTI"; "XOBJ"; "cacheI"; "dmS"; "entI"; "hw'"; "optR"; "regsI"; "updF"; "vMU"; "vNlo"; "BSHq"; "NXQI"; "OBJS_I"; "O_mag"; "QIENT"; "cls2T"; "clsQCT"; "clsT"; "cptrT"; "kAllocBegMagic"; "lenT"; "nT"; "post_ruI"; "qT"; "rup8T"; "s2T"; "sh255T"; "sh3T"; "slotI"; "szBigT"; "szSmallT"; "vSTK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "sdiff"; "one_at"; "diffs_below"; "entsI"; "two_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SRL"; "ALU_SLL"; "ALU_AND"; "ALU_SUB"; "BC_GEU"; "BC_EQ"; "M_MUL"; "ALU_OR"; "ALU_SLTU"; "ALU_SRA"; "ALU_XOR"; "BC_NE"; "M_DIVU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "vRIS"; "O_insta"; "O_insta2"; "O_rms";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kSpaceSize"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "mkA"; "stack_win"; "pre_facts"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "O_ctx98"; "O_rt1a"; "O_rt1b"; "O_self_tsd"; "O_tsd0"; "O_tsda"; "O_tsdb"; "O_tsdc"; "TP_A"; "vT"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Open Scope Z_scope.

Definition QIENT : Z := 0x3e764.
Definition QI0 : Z := 0x3e7b8.
Definition QI1 : Z := 0x3e814.
Definition QI2 : Z := 0x3e850.
Definition QI3 : Z := 0x3e88c.
Definition PSENT : Z := 0x5f750.
Definition MSENTQ : Z := 0xdb004.
Definition QCENTI : Z := 0x3eb68.
Definition QIRET : Z := 0x3ec08.
Definition NXI : positive := 200%positive.
Definition NXQI : positive := 260%positive.

Definition vMU := SVar 138. Definition vHW := SVar 139. Definition vNlo := SVar 141. Definition vSTK := SVar 142. Definition vN8 := SVar 145.
Definition vCLS : sv := SVar V_CLS. Definition vSZ : sv := SVar V_SIZE.
Definition cacheI : sv := add vT (SLit 208).

Definition O_cb : sobj := ltac2:(tb__ "0|4|
Se0S16PcA1Z0M0Z10S0S6S6SdS3A2M1S11A2M2S5G1S11S5SdS3G0U8M3A4Sa2A4S0G2S5G1S11S5SdS3Z8G3A4Sc0A4S2G2A1A3A3A4").
Definition O_rie : sobj := ltac2:(tb__ "0|1|
S20S38Se4S15ScaS40S12Z7A1A3A2S12Z30A1M0S12Z38A1S0S1aS1eG0Z8Sa9A3S2S1aA1A3S1fA5").
Definition O_hdrI (w : sv) : sobj := ltac2:(tb__ "0|4|
Se0S16PdA1Z0M0Z8S0S6S6SdS3A2M1S11A2M2S5G1S11S5SdS3G0U4M3A4Vw;A4S0G2S5G1S11S5SdS3Z4G3A4SaaA4S2G2A1A3A3A4").
Definition BSHq : sv := ltac2:(tb__ "0|0|
S38S15Sc9S38S16PdA1S12Z10A1A2S12Z3A1A3S12Z7fff8000A1A2").
Definition LENq : sv := SAlu ALU_SRL vN8 (SLit 3).
Definition O_ish : sobj := ltac2:(tb__ "0|0|
S20SabS12Z0A1S63S2S1aA1S1fA5").
Definition entI : sv := ltac2:(tb__ "0|0|
S38Sa2S28ScfS40S12Z50A1A3A2").
Definition O_entI (k : sv) : sobj := ltac2:(tb__ "0|3|
S20Sa4S12Z0A1M0S12Z10A1S0S1aS1eG0Z4M1Vk;A3S0S1aS1eS12G1A1G1S3cA3S0S1aS1eS12Z8M2A1G2S42A3S2S1aA1A3A3A3S1fA5").
Definition slotI : sv := ltac2:(tb__ "0|0|
S38Sa4S15ScaS3dS12Z2A1A3A2").
Definition O_slotI (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S20SbdS12Z10A1S12Z14A1Vcells;S1fA5").
Definition O_stq (v : sv) : sobj := ltac2:(tb__ "0|0|
S20SfbS12Zad0A1S12Zc60A1S0S1aS1eS12Zae0A1Z8Vv;A3S2S1aA1A3S1fA5").
Definition RTI : list sobj := ltac2:(tb__ "0|0|
S0S14Se5S0S14Se6S0S14Se7S0S14Sf7S0S14Sf8S0S14Sf9S0S14Sf5S0S14Sf6S0S14Sf2S0S14Sf3S0S14Sf4S2S14A1A3A3A3A3A3A3A3A3A3A3A3").

Definition vAB := SVar 146.
Definition kAllocBegMagic : Z := 0xCC6E96B9CC6E96B9.
Definition O_mag (w : sv) : sobj := ltac2:(tb__ "0|4|
Se0S90Z0M0Z10S0S6S6SdS3A2M1S11A2M2S5G1S11S5SdS3G0U8M3A4Vw;A4S0G2S5G1S11S5SdS3Z8G3A4S16PdA1A4S2G2A1A3A3A4").
Definition bgv (vb : bool) : sv := if vb then vAB else SVar 13.
Definition XOBJ (vb : bool) (w : sv) : list sobj := ltac2:(tb__ "0|1|
S1S8S14A1Lvb;Vvb;S0S14SaeVw;A1S2S14A1M0A3G0X1x2").
Definition XF (vb : bool) : list sprop := ltac2:(tb__ "0|1|
S1S8S13A1Lvb;Vvb;S0S13S1dP92Z4A2S0S13S19S3bS90A2S0S13S26S90S16PdA1A2S2S13A1M0A3A3A3G0X1x2").

Definition F_QI : list sprop := ltac2:(tb__ "0|9|
S9S13SedS3fA1S9S13Sf0S0S13S1dPdM0Z4M1A2S0S13S1dPcZ3M2A2S0S13S1dP9bZ10M3A2S0S13S19S12Se9A1S3bA2S0S13S19S3bS12SeeSeeZ7fffff800000M4Se8A2Z1000A2A1A2S0S13S1cSceSe4S38S3bS12Se8A1A2M5A3S0S13S19S12Z1A1S40A2S0S13S19S40S12Z1eA1A2S0S13S19S12G3A1M6S42A2S0S13S19S42S12Z10000A1A2S0S13S1dSf1G1A2S0S13S19S3bS16G0A1M7A2S0S13S26G7G5A2S0S13S22S1cSd4S15ScbS21S4Q20S91A3S12ZffA1A3S12G2A1A3A1S0S13S22S1cSceS3cS12Z0A1A3A1S0S13S26S3dS3cA2S0S13S19S3cS12Z100A1A2S0S13S19S12Z8A1S4dA2S0S13S19S4dS12SefZ2Z28A2A1A2S0S13S1dP91G2A2S0S13S19S38S38G7G6A2S4dA2M8G5A2S0S13S19G8S12G4A1A2S2S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition regsI : list sv := ltac2:(tb__ "0|1|
Sd7Sd9S0S6S3S11A2M0S5S3S11U4S12SfaA1A4S2G0A1A3A2").
Definition OBJS_I (hw : sv) (k : sv) (slot : list cell) (st : sv) : list sobj := ltac2:(tb__ "0|0|
S9S14S0S14SecSeaA3S9S14Sa0S0S14S98S0S14S9cS0S14S9aVhw;A1S0S14S9bS0S14S99Vk;A1S0S14S9dVslot;A1S0S14S9eVst;A1S2S14A1A3A3A3A3A3A3A3A3A3").
Definition PreQI (vb : bool) : axst := ltac2:(tb__ "0|0|
SebS23SafSa7Sd8S27SaS11A1S9S14SadS91S3dS2S1aA1S3eA4Sa1Vvb;S12Sb4A1A2A3S9S13S62S66Vvb;A1A3S3aS7A9S2S6S11S11A2A1A2").

Definition updQ (E : axst) (pc : Z) (ru : list (nat * sv)) : axst := ltac2:(tb__ "0|0|
S31VE;A1S2eS34VE;S23Vpc;Sd7S2cR1A1Vru;A2S2aR1A1S29R1A1S2dR1A1S2bR1A1S1bR1A1S17R1A1S18R1A1A9A2TS;").
Definition updF (E : axst) (pc : Z) (ru : list (nat * sv)) (F : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
S31VE;A1S2eS34VE;S23Vpc;Sd7S2cR1A1Vru;A2S2aR1A1S29R1A1S2dR1A1S2bR1A1VF;Vnx;S18R1A1A9A2TS;").

Definition dmS : sv := SAlu ALU_SUB (SVar 13) vSB.
Definition clsT : sv := ltac2:(tb__ "0|0|
S15ScbS15Sc9Sa3S12Z20A1A3S12Z1fA1A3").
Definition cls2T : sv := SAlu ALU_SRL dmS (SLit 32).
Definition szBigT : sv := ltac2:(tb__ "0|3|
S38S15ScbS15Sd2S15ScaS40S12Z3fA1M0A3G0A3S15Sc9S15ScaS12Z200A1S15Sc9S38S40S12N10A1A2S12Z1A1M1A3A3M2G1A3A3G2A2").
Definition szSmallT : sv := SAlu ALU_SLL vCLS (SLit 5).
Definition qT : sv := ltac2:(tb__ "0|1|
S15Sc9S15ScaS2fSd5Sa3S42A3S12Z20A1M0A3G0A3").
Definition s2T : sv := ltac2:(tb__ "0|1|
S15ScbS38S15Sd1Sa9S38S28ScfS42Sb8A3M0S42A2A3S12N1A1A2S38S38S15ScaS40S12Z20A1A3S3bA2G0A2A3").
Definition m8T : sv := SAlu ALU_SLL (SVar 13) (SLit 3).
Definition sh3T : sv := SAluW ALU_SLL (SLit 3) m8T.
Definition sh255T : sv := SAluW ALU_SLL (SLit 255) m8T.
Definition hw' : sv := ltac2:(tb__ "0|0|
S15Sd3S21S4Q20S91A3S12Z3A1A3").
Definition nT : sv := ltac2:(tb__ "0|0|
S15Sd0S15ScaS21S7Q10S15Sc9Sa5S12Z10A1A3A3S12Z20A1A3S21S7Q20SaaA3A3").
Definition rup8T : sv := ltac2:(tb__ "0|0|
S15ScbS38Sb6S12Z7A1A2S12Zfffffffffffffff8A1A3").
Definition lenT : sv := ltac2:(tb__ "0|2|
S15SccS38S15Sc9S38S38S38S16PdA1S12Z10A1A2M0S4dA2S12N8A1A2S12Z3A1M1A3S12Z1A1A2S15Sc9G0G1A3A3").
Definition clsQCT (vb : bool) : sv := ltac2:(tb__ "0|0|
S15Sc9S15ScaS15SccS53Vvb;A1S3bA3S12Z1bA1A3S12Z3bA1A3").
Definition cptrT (vb : bool) : sv := ltac2:(tb__ "0|0|
S15Sc9S15SccS15SccS53Vvb;A1S15ScaS40S12Z20A1A3A3S3bA3S12Z4A1A3").

Definition dI0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11Sb2S40A4S0G0S5S11S11Sb0S40A4S2G0A1A3A3").
Definition dI1a : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11SbeS42A4S2G0A1A3").
Definition dI1b : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11SbfS42A4S2G0A1A3").
Definition dI2 (vb : bool) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11SbaS53Vvb;A1A4S2G0A1A3").
Definition dI3 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11SbcS12Z3A1A4S0G0S5S11S11SbbS12ZffA1A4S2G0A1A3A3").
Definition dI4 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11Sb9S4dA4S2G0A1A3").
Definition dI5 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11Sb5S63A4S2G0A1A3").
Definition dI6 (vb : bool) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6S11S11A2M0S5S11S11Sb1Vvb;A1S40A4S2G0A1A3").

Definition optR (o : option (list sobj)) : list sobj := match o with Some r => r | None => [] end.

Definition post_ruI : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S3S11A2M0S5S3S11U0S16Pb8A1A4S0G0S5S3S11U5S16Pb9A1A4S0G0S5S3S11U6S16PbaA1A4S0G0S5S3S11U7S16PbbA1A4S0G0S5S3S11UaS16PbcA1A4S0G0S5S3S11UbS16PbdA1A4S0G0S5S3S11UcS16PbeA1A4S0G0S5S3S11UdS16PbfA1A4S0G0S5S3S11UeS16Pc0A1A4S0G0S5S3S11UfS16Pc1A1A4S0G0S5S3S11U10S16Pc2A1A4S0G0S5S3S11U11S16Pc3A1A4S0G0S5S3S11U1cS16Pc4A1A4S0G0S5S3S11U1dS16Pc5A1A4S0G0S5S3S11U1eS16Pc6A1A4S0G0S5S3S11U1fS16Pc7A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition PostQI (vb : bool) : axst := ltac2:(tb__ "0|1|
SebS23S75Sd7Sa7Sb7A2Sd8S27SaS11A1S0S14S9bS9S14S0S14SecSeaA3S9S14Sa0S9S14S0S14S98S0S14S9cS0S14S9aSa5A1S0S14S99S38S3dS12Z1A1A2A1S0S14S9dS0S1aS1eS12Z10A1Z4Sb3Vvb;A1A3S2S1aA1A3A1S0S14S9eS38S3eS15SccS12Z0A1M0S42A3A2A1S2S14A1A3A3A3A3A3A3Sa1Vvb;G0A2A3A3A3A3S9S13S62S66Vvb;A1A3SacS7A9S2S6S11S11A2A1A2").

Lemma preQI_wf : ltac2:(tb__ "0|2|
S1S10SfS1S36S52R1A1M0A1S4A3S10SfS1S30S31G0A1M1A1S4A3S10SfSeS17G1A1S3aA3SfS1S18G1A1S7A3A2A2A2Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma dI_below : ltac2:(tb__ "0|0|
S1S10SfS1Sc3S3aS7aA2S4A3S10SfS1Sc3S3aS7bA2S4A3S10SfS1Sc3S3aS7cA2S4A3S10SfS1Sc3S3aS7dR1A1A2S4A3S10SfS1Sc3S3aS7eA2S4A3S10SfS1Sc3S3aS7fA2S4A3S10SfS1Sc3S3aS80A2S4A3SfS1Sc3S3aS81R1A1A2S4A3A2A2A2A2A2A2A2Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run0a : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS4aS0SdZ3e7d0S2SdA1A3A3S52S7A1A3").
Definition E0a : axst := leaf 0 run0a.
Definition C0a : axst := ltac2:(tb__ "0|1|
S41S69S4aS0S6S3S11A2M0S5S3S11UcS40A4S0G0S5S3S11UdS40A4S2G0A1A3A3A3").
Definition run1a : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS44S0SdZ3e7d0S0SdZ3e9a4S0SdZ3e998S2SdA1A3A3A3A3S56A3").
Definition E1aa : axst := leaf 0 run1a.
Definition E1ba : axst := leaf 1 run1a.
Definition E1aa' : axst := ltac2:(tb__ "0|1|
S41S60S44S0S6S3S11A2M0S5S3S11UfS42A4S2G0A1A3A3").
Definition E1ba' : axst := ltac2:(tb__ "0|1|
S41S50S44S0S6S3S11A2M0S5S3S11UfS42A4S2G0A1A3A3").
Definition C1a : axst := ltac2:(tb__ "0|1|
Sa8S50S44S0S6S3S11A2M0S5S3S11UfS42A4S0G0S5S3S11U10S16Pb9A1A4S0G0S5S3S11U11S16PbaA1A4S2G0A1A3A3A3S9S13S62S66S7A1A3S43A5").
Definition run2a : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS4bS2SdA1A3S4eA3").
Definition E2a : axst := leaf 0 run2a.
Definition C2a : axst := ltac2:(tb__ "0|1|
S41S6bS4bS0S6S3S11A2M0S5S3S11U12S53S7A1A4S2G0A1A3A3").
Definition run3a : list leafA := ltac2:(tb__ "0|0|
S37U258S0SdS4cS0SdZ3e9acS0SdZ3e9d0S0SdZ3e8d0S2SdA1A3A3A3A3S58A3").
Definition E3a : axst := leaf 0 run3a.
Definition C3a : axst := ltac2:(tb__ "0|1|
S41S6dS4cS0S6S3S11A2M0S5S3S11UdS12Z3A1A4S0G0S5S3S11UeS12ZffA1A4S2G0A1A3A3A3").
Definition run4a : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS48S0SdZ3e9acS2SdA1A3A3S5aA3").
Definition E4a : axst := leaf 0 run4a.
Definition C4a : axst := ltac2:(tb__ "0|1|
S41S6fS48S0S6S3S11A2M0S5S3S11UbS4dA4S2G0A1A3A3").
Definition run5a : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS47S0SdZ3e8d0S0SdZ5fbd8S0SdZ5fbb8S0SdZ5fbf8S0SdZ5fc18S0SdZ5fb98S2SdA1A3A3A3A3A3A3A3S5cA3").
Definition E5a : axst := leaf 0 run5a.
Definition C5a : axst := ltac2:(tb__ "0|1|
S41S71S47S0S6S3S11A2M0S5S3S11UcS63A4S2G0A1A3A3").
Definition s5a : wsub := ltac2:(tb__ "0|0|
Se2P1S31S45A1S31Sc6A1A3").
Definition R5a : list sobj := ltac2:(tb__ "0|0|
Sa6SdaS45Sc6S54A3A1").
Definition T5a : axst := ltac2:(tb__ "0|0|
SdbS54Sc6Sd6SddSc7A1A1S45S64A5").
Definition T5fa : axst := ltac2:(tb__ "0|0|
Se3S76S1bS31S45A1A1A2").
Definition run6a : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS49S0SdZ3e94cS0SdZ3e96cS2SdA1A3A3A3S78A3").
Definition E6a : axst := leaf 0 run6a.
Definition C6a : axst := ltac2:(tb__ "0|1|
S41S73S49S0S6S3S11A2M0S5S3S11UcS40A4S2G0A1A3A3").
Definition run7a : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdZ3ecf8S0SdZ3ec50S0SdZ3ec0cS0SdZ3ec2cS2SdA1A3A3A3A3S5eA3").
Definition E7a : axst := leaf 0 run7a.

Lemma run0a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS4aS0SdZ3e7d0S2SdA1A3A3S52S7A1A3S82A3"). Proof. unfold run0a. reflexivity. Qed.
Lemma chk0a : ltac2:(tb__ "0|0|
SfS1Sc2S82S4aA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd0a : ltac2:(tb__ "0|0|
SfS1Sc1S69S56S7aA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run1a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS44S0SdZ3e7d0S0SdZ3e9a4S0SdZ3e998S2SdA1A3A3A3A3S56A3S67A3"). Proof. unfold run1a. reflexivity. Qed.
Lemma chk1a : ltac2:(tb__ "0|0|
SfS1Sc5S67S44A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd1aa : ltac2:(tb__ "0|0|
SfS1Sc1S60S92S7bA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd1ba : ltac2:(tb__ "0|0|
SfS1Sc1S50S94S7cA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent1aa : ltac2:(tb__ "0|0|
SfS1Sc4S92S4eA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent1ba : ltac2:(tb__ "0|0|
SfS1Sc4S94S4eA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma br1aa : ltac2:(tb__ "0|0|
SfS1SdeS13S25S1cScdS40S12Z11A1A3A1S1bS31S60A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma br1ba : ltac2:(tb__ "0|0|
SfS1SdeS13S25S22S1cScdS40S12Z11A1A3A1A1S1bS31S50A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run2a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS4bS2SdA1A3S4eA3S84A3"). Proof. unfold run2a. reflexivity. Qed.
Lemma chk2a : ltac2:(tb__ "0|0|
SfS1Sc2S84S4bA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd2a : ltac2:(tb__ "0|0|
SfS1Sc1S6bS58S7dS7A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run3a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U258S0SdS4cS0SdZ3e9acS0SdZ3e9d0S0SdZ3e8d0S2SdA1A3A3A3A3S58A3S86A3"). Proof. unfold run3a. reflexivity. Qed.
Lemma chk3a : ltac2:(tb__ "0|0|
SfS1Sc2S86S4cA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd3a : ltac2:(tb__ "0|0|
SfS1Sc1S6dS5aS7eA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run4a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS48S0SdZ3e9acS2SdA1A3A3S5aA3S88A3"). Proof. unfold run4a. reflexivity. Qed.
Lemma chk4a : ltac2:(tb__ "0|0|
SfS1Sc2S88S48A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd4a : ltac2:(tb__ "0|0|
SfS1Sc1S6fS5cS7fA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run5a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS47S0SdZ3e8d0S0SdZ5fbd8S0SdZ5fbb8S0SdZ5fbf8S0SdZ5fc18S0SdZ5fb98S2SdA1A3A3A3A3A3A3A3S5cA3S8aA3"). Proof. unfold run5a. reflexivity. Qed.
Lemma chk5a : ltac2:(tb__ "0|0|
SfS1Sc2S8aS47A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd5a : ltac2:(tb__ "0|0|
SfS1Sc1S71S45S80A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma He5a : ltac2:(tb__ "0|1|
SfScS8S14A1M0A1SdaS45Sc6S54A3SbG0S64A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk5a : ltac2:(tb__ "0|0|
SfS1SdcS45Sc6S54S64Se1S33S32S35Sc8A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT5a : ltac2:(tb__ "0|0|
SfS32SdbS54Sc6Sd6SddSc7A1A1S45S64A5S76A3"). Proof. unfold T5a. reflexivity. Qed.
Lemma FBC5a : ltac2:(tb__ "0|1|
SfS1SdfS13S24S17S31S45A1M0A1A1S1bG0A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT5a : ltac2:(tb__ "0|0|
SfS1SdfS13S24S17S31S76A1A1A1S1bS31S45A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run6a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS49S0SdZ3e94cS0SdZ3e96cS2SdA1A3A3A3S78A3S8cA3"). Proof. unfold run6a. reflexivity. Qed.
Lemma chk6a : ltac2:(tb__ "0|0|
SfS1Sc2S8cS49A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd6a : ltac2:(tb__ "0|0|
SfS1Sc1S73S5eS81S7A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run7a_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdZ3ecf8S0SdZ3ec50S0SdZ3ec0cS0SdZ3ec2cS2SdA1A3A3A3A3S5eA3S8eA3"). Proof. unfold run7a. reflexivity. Qed.
Lemma chk7a : ltac2:(tb__ "0|0|
SfS1Sc2S8eS75A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent7a : ltac2:(tb__ "0|0|
SfS1Sc4S96S9fS7A1A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nxC0a : ltac2:(tb__ "0|1|
S10SfSeS17S31S56A1M0A1S3aA3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC1a : ltac2:(tb__ "0|1|
S10SfSeS17S31S4eA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC2a : ltac2:(tb__ "0|1|
S10SfSeS17S31S58A1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC3a : ltac2:(tb__ "0|1|
S10SfSeS17S31S5aA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC4a : ltac2:(tb__ "0|1|
S10SfSeS17S31S5cA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC5a : ltac2:(tb__ "0|1|
S10SfSeS17S31S45A1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxT5fa : ltac2:(tb__ "0|1|
S10SfSeS17S31S78A1M0A1Pf0A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC6a : ltac2:(tb__ "0|1|
S10SfSeS17S31S5eA1M0A1Pf2A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma E0a_def : ltac2:(tb__ "0|0|
SfS32S39U0S82A2S69A3"). Proof. unfold E0a. reflexivity. Qed.
Lemma E1aa_def : ltac2:(tb__ "0|0|
SfS32S39U0S67A2S60A3"). Proof. unfold E1aa. reflexivity. Qed.
Lemma E1ba_def : ltac2:(tb__ "0|0|
SfS32S39U1S67A2S50A3"). Proof. unfold E1ba. reflexivity. Qed.
Lemma E2a_def : ltac2:(tb__ "0|0|
SfS32S39U0S84A2S6bA3"). Proof. unfold E2a. reflexivity. Qed.
Lemma E3a_def : ltac2:(tb__ "0|0|
SfS32S39U0S86A2S6dA3"). Proof. unfold E3a. reflexivity. Qed.
Lemma E4a_def : ltac2:(tb__ "0|0|
SfS32S39U0S88A2S6fA3"). Proof. unfold E4a. reflexivity. Qed.
Lemma E5a_def : ltac2:(tb__ "0|0|
SfS32S39U0S8aA2S71A3"). Proof. unfold E5a. reflexivity. Qed.
Lemma E6a_def : ltac2:(tb__ "0|0|
SfS32S39U0S8cA2S73A3"). Proof. unfold E6a. reflexivity. Qed.
Lemma E7a_def : ltac2:(tb__ "0|0|
SfS32S39U0S8eA2S96A3"). Proof. unfold E7a. reflexivity. Qed.

Definition run0b : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS4aS0SdZ3e7d0S2SdA1A3A3S52S4A1A3").
Definition E0b : axst := leaf 0 run0b.
Definition C0b : axst := ltac2:(tb__ "0|1|
S41S6aS4aS0S6S3S11A2M0S5S3S11UcS40A4S0G0S5S3S11UdS40A4S2G0A1A3A3A3").
Definition run1b : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS44S0SdZ3e7d0S0SdZ3e9a4S0SdZ3e998S2SdA1A3A3A3A3S57A3").
Definition E1ab : axst := leaf 0 run1b.
Definition E1bb : axst := leaf 1 run1b.
Definition E1ab' : axst := ltac2:(tb__ "0|1|
S41S61S44S0S6S3S11A2M0S5S3S11UfS42A4S2G0A1A3A3").
Definition E1bb' : axst := ltac2:(tb__ "0|1|
S41S51S44S0S6S3S11A2M0S5S3S11UfS42A4S2G0A1A3A3").
Definition C1b : axst := ltac2:(tb__ "0|1|
Sa8S51S44S0S6S3S11A2M0S5S3S11UfS42A4S0G0S5S3S11U10S16Pb9A1A4S0G0S5S3S11U11S16PbaA1A4S2G0A1A3A3A3S9S13S62S66S4A1A3S43A5").
Definition run2b : list leafA := ltac2:(tb__ "0|0|
S37U12cS0SdS4bS2SdA1A3S4fA3").
Definition E2b : axst := leaf 0 run2b.
Definition C2b : axst := ltac2:(tb__ "0|1|
S41S6cS4bS0S6S3S11A2M0S5S3S11U12S53S4A1A4S2G0A1A3A3").
Definition run3b : list leafA := ltac2:(tb__ "0|0|
S37U258S0SdS4cS0SdZ3e9acS0SdZ3e9d0S0SdZ3e8d0S2SdA1A3A3A3A3S59A3").
Definition E3b : axst := leaf 0 run3b.
Definition C3b : axst := ltac2:(tb__ "0|1|
S41S6eS4cS0S6S3S11A2M0S5S3S11UdS12Z3A1A4S0G0S5S3S11UeS12ZffA1A4S2G0A1A3A3A3").
Definition run4b : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS48S0SdZ3e9acS2SdA1A3A3S5bA3").
Definition E4b : axst := leaf 0 run4b.
Definition C4b : axst := ltac2:(tb__ "0|1|
S41S70S48S0S6S3S11A2M0S5S3S11UbS4dA4S2G0A1A3A3").
Definition run5b : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS47S0SdZ3e8d0S0SdZ5fbd8S0SdZ5fbb8S0SdZ5fbf8S0SdZ5fc18S0SdZ5fb98S2SdA1A3A3A3A3A3A3A3S5dA3").
Definition E5b : axst := leaf 0 run5b.
Definition C5b : axst := ltac2:(tb__ "0|1|
S41S72S47S0S6S3S11A2M0S5S3S11UcS63A4S2G0A1A3A3").
Definition s5b : wsub := ltac2:(tb__ "0|0|
Se2P1S31S46A1S31Sc6A1A3").
Definition R5b : list sobj := ltac2:(tb__ "0|0|
Sa6SdaS46Sc6S55A3A1").
Definition T5b : axst := ltac2:(tb__ "0|0|
SdbS55Sc6Sd6SddSc7A1A1S46S65A5").
Definition T5fb : axst := ltac2:(tb__ "0|0|
Se3S77S1bS31S46A1A1A2").
Definition run6b : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdS49S0SdZ3e94cS0SdZ3e96cS2SdA1A3A3A3S79A3").
Definition E6b : axst := leaf 0 run6b.
Definition C6b : axst := ltac2:(tb__ "0|1|
S41S74S49S0S6S3S11A2M0S5S3S11UcS40A4S2G0A1A3A3").
Definition run7b : list leafA := ltac2:(tb__ "0|0|
S37U320S0SdZ3ecf8S0SdZ3ec50S0SdZ3ec0cS0SdZ3ec2cS2SdA1A3A3A3A3S5fA3").
Definition E7b : axst := leaf 0 run7b.

Lemma run0b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS4aS0SdZ3e7d0S2SdA1A3A3S52S4A1A3S83A3"). Proof. unfold run0b. reflexivity. Qed.
Lemma chk0b : ltac2:(tb__ "0|0|
SfS1Sc2S83S4aA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd0b : ltac2:(tb__ "0|0|
SfS1Sc1S6aS57S7aA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run1b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS44S0SdZ3e7d0S0SdZ3e9a4S0SdZ3e998S2SdA1A3A3A3A3S57A3S68A3"). Proof. unfold run1b. reflexivity. Qed.
Lemma chk1b : ltac2:(tb__ "0|0|
SfS1Sc5S68S44A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd1ab : ltac2:(tb__ "0|0|
SfS1Sc1S61S93S7bA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd1bb : ltac2:(tb__ "0|0|
SfS1Sc1S51S95S7cA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent1ab : ltac2:(tb__ "0|0|
SfS1Sc4S93S4fA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent1bb : ltac2:(tb__ "0|0|
SfS1Sc4S95S4fA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma br1ab : ltac2:(tb__ "0|0|
SfS1SdeS13S25S1cScdS40S12Z11A1A3A1S1bS31S61A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma br1bb : ltac2:(tb__ "0|0|
SfS1SdeS13S25S22S1cScdS40S12Z11A1A3A1A1S1bS31S51A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run2b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U12cS0SdS4bS2SdA1A3S4fA3S85A3"). Proof. unfold run2b. reflexivity. Qed.
Lemma chk2b : ltac2:(tb__ "0|0|
SfS1Sc2S85S4bA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd2b : ltac2:(tb__ "0|0|
SfS1Sc1S6cS59S7dS4A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run3b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U258S0SdS4cS0SdZ3e9acS0SdZ3e9d0S0SdZ3e8d0S2SdA1A3A3A3A3S59A3S87A3"). Proof. unfold run3b. reflexivity. Qed.
Lemma chk3b : ltac2:(tb__ "0|0|
SfS1Sc2S87S4cA2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd3b : ltac2:(tb__ "0|0|
SfS1Sc1S6eS5bS7eA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run4b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS48S0SdZ3e9acS2SdA1A3A3S5bA3S89A3"). Proof. unfold run4b. reflexivity. Qed.
Lemma chk4b : ltac2:(tb__ "0|0|
SfS1Sc2S89S48A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd4b : ltac2:(tb__ "0|0|
SfS1Sc1S70S5dS7fA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run5b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS47S0SdZ3e8d0S0SdZ5fbd8S0SdZ5fbb8S0SdZ5fbf8S0SdZ5fc18S0SdZ5fb98S2SdA1A3A3A3A3A3A3A3S5dA3S8bA3"). Proof. unfold run5b. reflexivity. Qed.
Lemma chk5b : ltac2:(tb__ "0|0|
SfS1Sc2S8bS47A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd5b : ltac2:(tb__ "0|0|
SfS1Sc1S72S46S80A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma He5b : ltac2:(tb__ "0|1|
SfScS8S14A1M0A1SdaS46Sc6S55A3SbG0S65A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk5b : ltac2:(tb__ "0|0|
SfS1SdcS46Sc6S55S65Se1S33S32S35Sc8A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT5b : ltac2:(tb__ "0|0|
SfS32SdbS55Sc6Sd6SddSc7A1A1S46S65A5S77A3"). Proof. unfold T5b. reflexivity. Qed.
Lemma FBC5b : ltac2:(tb__ "0|1|
SfS1SdfS13S24S17S31S46A1M0A1A1S1bG0A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT5b : ltac2:(tb__ "0|0|
SfS1SdfS13S24S17S31S77A1A1A1S1bS31S46A1A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run6b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdS49S0SdZ3e94cS0SdZ3e96cS2SdA1A3A3A3S79A3S8dA3"). Proof. unfold run6b. reflexivity. Qed.
Lemma chk6b : ltac2:(tb__ "0|0|
SfS1Sc2S8dS49A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sd6b : ltac2:(tb__ "0|0|
SfS1Sc1S74S5fS81S4A1A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run7b_eq : ltac2:(tb__ "0|0|
SfS8S33A1S37U320S0SdZ3ecf8S0SdZ3ec50S0SdZ3ec0cS0SdZ3ec2cS2SdA1A3A3A3A3S5fA3S8fA3"). Proof. unfold run7b. reflexivity. Qed.
Lemma chk7b : ltac2:(tb__ "0|0|
SfS1Sc2S8fS75A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent7b : ltac2:(tb__ "0|0|
SfS1Sc4S97S9fS4A1A2S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nxC0b : ltac2:(tb__ "0|1|
S10SfSeS17S31S57A1M0A1S3aA3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC1b : ltac2:(tb__ "0|1|
S10SfSeS17S31S4fA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC2b : ltac2:(tb__ "0|1|
S10SfSeS17S31S59A1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC3b : ltac2:(tb__ "0|1|
S10SfSeS17S31S5bA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC4b : ltac2:(tb__ "0|1|
S10SfSeS17S31S5dA1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC5b : ltac2:(tb__ "0|1|
S10SfSeS17S31S46A1M0A1S43A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxT5fb : ltac2:(tb__ "0|1|
S10SfSeS17S31S79A1M0A1Pf0A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma nxC6b : ltac2:(tb__ "0|1|
S10SfSeS17S31S5fA1M0A1Pf2A3SfS1S18G0A1S7A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma E0b_def : ltac2:(tb__ "0|0|
SfS32S39U0S83A2S6aA3"). Proof. unfold E0b. reflexivity. Qed.
Lemma E1ab_def : ltac2:(tb__ "0|0|
SfS32S39U0S68A2S61A3"). Proof. unfold E1ab. reflexivity. Qed.
Lemma E1bb_def : ltac2:(tb__ "0|0|
SfS32S39U1S68A2S51A3"). Proof. unfold E1bb. reflexivity. Qed.
Lemma E2b_def : ltac2:(tb__ "0|0|
SfS32S39U0S85A2S6cA3"). Proof. unfold E2b. reflexivity. Qed.
Lemma E3b_def : ltac2:(tb__ "0|0|
SfS32S39U0S87A2S6eA3"). Proof. unfold E3b. reflexivity. Qed.
Lemma E4b_def : ltac2:(tb__ "0|0|
SfS32S39U0S89A2S70A3"). Proof. unfold E4b. reflexivity. Qed.
Lemma E5b_def : ltac2:(tb__ "0|0|
SfS32S39U0S8bA2S72A3"). Proof. unfold E5b. reflexivity. Qed.
Lemma E6b_def : ltac2:(tb__ "0|0|
SfS32S39U0S8dA2S74A3"). Proof. unfold E6b. reflexivity. Qed.
Lemma E7b_def : ltac2:(tb__ "0|0|
SfS32S39U0S8fA2S97A3"). Proof. unfold E7b. reflexivity. Qed.
End SegQI_states.

(* [comment removed for export] *)
Module F0A_c0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "sprop_below"; "swf"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "F_typ"; "PostQ1"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0A"; "C4_0A"; "EQ_0A"; "q_0A"; "C2_0A_1"; "C2_0A_2"; "C3_0A"; "CD_0A"; "ED_0A_1"; "ED_0A_2"; "P0_0A"; "Ems_0A"; "Eps_0A"; "S1c_0A_1"; "S1c_0A_2"; "TM_0A"; "TQ_0A"; "run3_0A"; "run6_0A"; "RM_0A"; "RQ_0A"; "TM0_0A"; "TQ0_0A"; "run2_0A_1"; "run2_0A_2"; "run4_0A"; "run5_0A"; "EfD_0A_1"; "EfD_0A_2"; "Eq_0A"; "RD_0A_1"; "RD_0A_2"; "TDr_0A_1"; "TDr_0A_2"; "exits1_0A"; "run1_0A"; "Ebg_0A"; "Edr_0A"; "TD_0A_1"; "TD_0A_2"; "Xf_0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_0A : list ulink := Wcan 0.
Definition st_0A : ustop := UStopLe.
Definition q_0A : qvar := QA.
Definition P0_0A : axst := P0_f W_0A st_0A q_0A.

Definition run1_0A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S21SbS2A1A3S40A3").

Definition S1c_0A_1 : axst := ltac2:(tb__ "0|0|
S2cS36U0S59A2S17S5S40A1A1Z1A3").
Definition C2_0A_1 : axst := C2_of S1c_0A_1.
Definition run2_0A_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3aA3").
Definition EfD_0A_1 : axst := leaf 0 run2_0A_1.
Definition ED_0A_1 : axst := ED_of EfD_0A_1.
Definition RD_0A_1 : list sobj := RD_of ED_0A_1 1.
Definition TD_0A_1 : axst := TD_of ED_0A_1 1.
Definition TDr_0A_1 : axst := TDr_of TD_0A_1.
Definition S1c_0A_2 : axst := ltac2:(tb__ "0|0|
S2cS36U0S59A2S17S5S40A1A1Z2A3").
Definition C2_0A_2 : axst := C2_of S1c_0A_2.
Definition run2_0A_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_0A_2 : axst := leaf 0 run2_0A_2.
Definition ED_0A_2 : axst := ED_of EfD_0A_2.
Definition RD_0A_2 : list sobj := RD_of ED_0A_2 2.
Definition TD_0A_2 : axst := TD_of ED_0A_2 2.
Definition TDr_0A_2 : axst := TDr_of TD_0A_2.
Definition exits1_0A : list axst := ltac2:(tb__ "0|0|
SaS4S43SaS4S44SbS4A1A3A3").

Definition CD_0A : axst := CD_of TDr_0A_1.
Definition run3_0A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S25SaS2S20SbS2A1A3A3S3dA3").
Definition Eps_0A : axst := leaf 0 run3_0A.
Definition Ebg_0A : axst := leaf 1 run3_0A.
Definition C3_0A : axst := C3_of Eps_0A.
Definition run4_0A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S24SbS2A1A3S3cA3").
Definition Ems_0A : axst := leaf 0 run4_0A.
Definition C4_0A : axst := C4_of Ems_0A.
Definition RM_0A : list sobj := RM_of C4_0A.
Definition TM0_0A : axst := TM0_of C4_0A.
Definition TM_0A : axst := TM_of C4_0A.
Definition run5_0A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S23SbS2A1A3S45A3").
Definition Eq_0A : axst := leaf 0 run5_0A.
Definition EQ_0A : axst := EQ_of Eq_0A.
Definition RQ_0A : list sobj := RQ_of EQ_0A q_0A.
Definition TQ0_0A : axst := TQ0_of EQ_0A q_0A.
Definition TQ_0A : axst := TQ_of EQ_0A q_0A.
Definition run6_0A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S22SaS2S27SbS2A1A3A3S46A3").
Definition Edr_0A : axst := leaf 0 run6_0A.
Definition Xf_0A : axst := leaf 1 run6_0A.

Ltac vmr := vm_compute; reflexivity.
Lemma Cert1_0A : ltac2:(tb__ "0|0|
S0S9S6fS60S1cSaS2S21SbS2A1A3S5fSaS4S40SbS4A1A3S58A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_0A exits1_0A run1_0A); [unfold run1_0A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_0A : ltac2:(tb__ "0|2|
S0S9S70S60S1cSaS2S21SbS2A1A3S5fSaS6dS6eS40Z1S1bZ0M0A1M1A3SbS6dA1A3S71S4S6dS4S6eR1G0G1A3LE;S58A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_0A 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_0A) run1_0A); [unfold run1_0A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_0A_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S63S5S43A1S5S3aA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_0A_1 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_0A_1 : ltac2:(tb__ "0|0|
S0S9S61S5fS13S5S3aA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_0A_1 : ltac2:(tb__ "0|0|
S0S4S7S43S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma RUN2_0A_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3aA3S4dA3"). Proof. unfold run2_0A_1; reflexivity. Qed.
Lemma L2_0A_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS4dSaS2S1dSbS2A1A3A2ScA3S0S4S36U0S4dA2S51A3A2"). Proof. Time (split; [vmr | unfold EfD_0A_1; reflexivity]). Qed.
Lemma AXD_0A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S62S51S2dA2SeS4S3eA2A3"). Proof. Time vmr. Qed.
Lemma HeD_0A_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S64S3eS68Z1M1A1S1fS3eG1A2A3SeG0S54A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_0A_1 : ltac2:(tb__ "0|1|
S0S9S66S3eS68Z1M0A1S1fS3eG0A2S54SaS4S69G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_0A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S62S5cS2eA2SeS4S56A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_0A_1 : ltac2:(tb__ "0|0|
S0S9S73S56S3dA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_0A_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S63S5S44A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_0A_2 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_0A_2 : ltac2:(tb__ "0|0|
S0S9S61S5fS13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_0A_2 : ltac2:(tb__ "0|0|
S0S4S7S44S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_0A_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3bA3S4eA3"). Proof. unfold run2_0A_2; reflexivity. Qed.
Lemma L2_0A_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS4eSaS2S1dSbS2A1A3A2ScA3S0S4S36U0S4eA2S52A3A2"). Proof. Time (split; [vmr | unfold EfD_0A_2; reflexivity]). Qed.
Lemma AXD_0A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S62S52S2dA2SeS4S3fA2A3"). Proof. Time vmr. Qed.
Lemma HeD_0A_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S64S3fS68Z2M1A1S1fS3fG1A2A3SeG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_0A_2 : ltac2:(tb__ "0|1|
S0S9S66S3fS68Z2M0A1S1fS3fG0A2S55SaS4S69G0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_0A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S62S5dS2eA2SeS4S57A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_0A_2 : ltac2:(tb__ "0|0|
S0S9S73S57S3dA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_0A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S25SaS2S20SbS2A1A3A3S3dA3S47A3"). Proof. unfold run3_0A; reflexivity. Qed.
Lemma L3_0A : ltac2:(tb__ "0|0|
S1S0S9S1eS47SaS2S25SaS2S20SbS2A1A3A3A2ScA3S1S0S4S36U0S47A2S42A3S0S4S36U1S47A2S5aA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_0A | unfold Ebg_0A]; reflexivity]). Qed.
Lemma NX3_0A : ltac2:(tb__ "0|1|
S1S0S9S61S5fS13S5S3dA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_0A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S63S5S42A1S5S3cA1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_0A : ltac2:(tb__ "0|0|
S0S4S7S42S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma NX3b_0A : ltac2:(tb__ "0|0|
S0S9S61S5fS13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_0A : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S42A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma RUN4_0A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S24SbS2A1A3S3cA3S4fA3"). Proof. unfold run4_0A; reflexivity. Qed.
Lemma L4_0A : ltac2:(tb__ "0|0|
S1S0S9S1eS4fSaS2S24SbS2A1A3A2ScA3S0S4S36U0S4fA2S41A3A2"). Proof. Time (split; [vmr | unfold Ems_0A; reflexivity]). Qed.
Lemma D4_0A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S63S5S41A1S5S37A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_0A : ltac2:(tb__ "0|0|
S0S4S7S41S5S37A1A2S37A3"). Proof. vmr. Qed.
Lemma W4_0A : ltac2:(tb__ "0|1|
S1S0S9S1aS5S37A1M0A1ScA3S1S0S3S13G0A1S13S5S41A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma HeM_0A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S64S37S6bS28S37A1A3SeG0S49A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_0A : ltac2:(tb__ "0|0|
S0S9S65S37S6bS28S37A1S49S71S6S4S8S6cA4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_0A : ltac2:(tb__ "0|0|
S0S4S67S28S37A1S6bS31S37S49A5S4bA3"). Proof. unfold TM0_0A, TM0_of, RM_0A; reflexivity. Qed.
Lemma FBM_0A : ltac2:(tb__ "0|3|
S1S0S9S6aS15S19S13S5S37A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6aS15S19S13S5S4bA1A1A1G2A3ScA3S0S9S61S5fG1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETM_0A : ltac2:(tb__ "0|0|
S0S4S72S4bS17S5S37A1A1A2S45A3"). Proof. vmr. Qed.
Lemma NX5_0A : ltac2:(tb__ "0|1|
S1S0S9S61S5fS13S5S45A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_0A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S23SbS2A1A3S45A3S50A3"). Proof. unfold run5_0A; reflexivity. Qed.
Lemma L5_0A : ltac2:(tb__ "0|0|
S1S0S9S1eS50SaS2S23SbS2A1A3A2ScA3S0S4S36U0S50A2S53A3A2"). Proof. Time (split; [vmr | unfold Eq_0A; reflexivity]). Qed.
Lemma AXQ_0A : ltac2:(tb__ "0|0|
S0SfS4A1S62S53S32A2SeS4S38A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_0A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S64S38S26S39A1S29S38S39A2A3SeG0S4aA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_0A : ltac2:(tb__ "0|0|
S0S9S65S38S26S39A1S29S38S39A2S4aSaS4S2bS39A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_0A : ltac2:(tb__ "0|0|
S0S4S67S29S38S39A2S26S39A1S2bS39A1S38S4aA5S4cA3"). Proof. unfold TQ0_0A, TQ0_of, RQ_0A; reflexivity. Qed.
Lemma FBQ_0A : ltac2:(tb__ "0|3|
S1S0S9S6aS15S19S13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6aS15S19S13S5S4cA1A1A1G2A3ScA3S0S9S61S5fG1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETQ_0A : ltac2:(tb__ "0|0|
S0S4S72S4cS17S5S38A1A1A2S46A3"). Proof. vmr. Qed.
Lemma NX6_0A : ltac2:(tb__ "0|1|
S1S0S9S61S5fS13S5S46A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_0A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S22SaS2S27SbS2A1A3A3S46A3S48A3"). Proof. unfold run6_0A; reflexivity. Qed.
Lemma L6_0A : ltac2:(tb__ "0|0|
S1S0S9S1eS48SaS2S22SaS2S27SbS2A1A3A3A2ScA3S1S0S4S36U0S48A2S5bA3S0S4S36U1S48A2S5eA3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_0A | unfold Xf_0A]; reflexivity]). Qed.

End F0A_c0A.

(* [comment removed for export] *)
Module F0A_c0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "sprop_below"; "swf"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "F_typ"; "PostQ1"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Be"; "C4_0Be"; "EQ_0Be"; "q_0Be"; "C2_0Be_1"; "C2_0Be_2"; "C3_0Be"; "CD_0Be"; "ED_0Be_1"; "ED_0Be_2"; "P0_0Be"; "Ems_0Be"; "Eps_0Be"; "S1c_0Be_1"; "S1c_0Be_2"; "TM_0Be"; "TQ_0Be"; "run3_0Be"; "run6_0Be"; "RM_0Be"; "RQ_0Be"; "TM0_0Be"; "TQ0_0Be"; "run2_0Be_1"; "run2_0Be_2"; "run4_0Be"; "run5_0Be"; "EfD_0Be_1"; "EfD_0Be_2"; "Eq_0Be"; "RD_0Be_1"; "RD_0Be_2"; "TDr_0Be_1"; "TDr_0Be_2"; "exits1_0Be"; "run1_0Be"; "Ebg_0Be"; "Edr_0Be"; "TD_0Be_1"; "TD_0Be_2"; "W_0Be"; "Xf_0Be"; "st_0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_0Be : list ulink := Wcan 0.
Definition st_0Be : ustop := UStopLe.
Definition q_0Be : qvar := QBe.
Definition P0_0Be : axst := ltac2:(tb__ "0|0|
S31S5fS61S3aA3").

Definition run1_0Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S21SbS2A1A3S41A3").

Definition S1c_0Be_1 : axst := ltac2:(tb__ "0|0|
S2cS37U0S5aA2S17S5S41A1A1Z1A3").
Definition C2_0Be_1 : axst := C2_of S1c_0Be_1.
Definition run2_0Be_1 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_0Be_1 : axst := leaf 0 run2_0Be_1.
Definition ED_0Be_1 : axst := ED_of EfD_0Be_1.
Definition RD_0Be_1 : list sobj := RD_of ED_0Be_1 1.
Definition TD_0Be_1 : axst := TD_of ED_0Be_1 1.
Definition TDr_0Be_1 : axst := TDr_of TD_0Be_1.
Definition S1c_0Be_2 : axst := ltac2:(tb__ "0|0|
S2cS37U0S5aA2S17S5S41A1A1Z2A3").
Definition C2_0Be_2 : axst := C2_of S1c_0Be_2.
Definition run2_0Be_2 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_0Be_2 : axst := leaf 0 run2_0Be_2.
Definition ED_0Be_2 : axst := ED_of EfD_0Be_2.
Definition RD_0Be_2 : list sobj := RD_of ED_0Be_2 2.
Definition TD_0Be_2 : axst := TD_of ED_0Be_2 2.
Definition TDr_0Be_2 : axst := TDr_of TD_0Be_2.
Definition exits1_0Be : list axst := ltac2:(tb__ "0|0|
SaS4S44SaS4S45SbS4A1A3A3").

Definition CD_0Be : axst := CD_of TDr_0Be_1.
Definition run3_0Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S25SaS2S20SbS2A1A3A3S3eA3").
Definition Eps_0Be : axst := leaf 0 run3_0Be.
Definition Ebg_0Be : axst := leaf 1 run3_0Be.
Definition C3_0Be : axst := C3_of Eps_0Be.
Definition run4_0Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S24SbS2A1A3S3dA3").
Definition Ems_0Be : axst := leaf 0 run4_0Be.
Definition C4_0Be : axst := C4_of Ems_0Be.
Definition RM_0Be : list sobj := RM_of C4_0Be.
Definition TM0_0Be : axst := TM0_of C4_0Be.
Definition TM_0Be : axst := TM_of C4_0Be.
Definition run5_0Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S23SbS2A1A3S46A3").
Definition Eq_0Be : axst := leaf 0 run5_0Be.
Definition EQ_0Be : axst := EQ_of Eq_0Be.
Definition RQ_0Be : list sobj := RQ_of EQ_0Be q_0Be.
Definition TQ0_0Be : axst := TQ0_of EQ_0Be q_0Be.
Definition TQ_0Be : axst := TQ_of EQ_0Be q_0Be.
Definition run6_0Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S22SaS2S27SbS2A1A3A3S47A3").
Definition Edr_0Be : axst := leaf 0 run6_0Be.
Definition Xf_0Be : axst := leaf 1 run6_0Be.

Ltac vmr := vm_compute; reflexivity.
Lemma Cert1_0Be : ltac2:(tb__ "0|0|
S0S9S72S63S1cSaS2S21SbS2A1A3S62SaS4S41SbS4A1A3S59A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_0Be exits1_0Be run1_0Be); [unfold run1_0Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_0Be : ltac2:(tb__ "0|2|
S0S9S73S63S1cSaS2S21SbS2A1A3S62SaS70S71S41Z1S1bZ0M0A1M1A3SbS70A1A3S74S4S70S4S71R1G0G1A3LE;S59A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_0Be 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_0Be) run1_0Be); [unfold run1_0Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_0Be_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S66S5S44A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_0Be_1 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_0Be_1 : ltac2:(tb__ "0|0|
S0S9S64S62S13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_0Be_1 : ltac2:(tb__ "0|0|
S0S4S7S44S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_0Be_1 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3bA3S4eA3"). Proof. unfold run2_0Be_1; reflexivity. Qed.
Lemma L2_0Be_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS4eSaS2S1dSbS2A1A3A2ScA3S0S4S37U0S4eA2S52A3A2"). Proof. Time (split; [vmr | unfold EfD_0Be_1; reflexivity]). Qed.
Lemma AXD_0Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S65S52S2dA2SeS4S3fA2A3"). Proof. Time vmr. Qed.
Lemma HeD_0Be_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S67S3fS6bZ1M1A1S1fS3fG1A2A3SeG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_0Be_1 : ltac2:(tb__ "0|1|
S0S9S69S3fS6bZ1M0A1S1fS3fG0A2S55SaS4S6cG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_0Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S65S5dS2eA2SeS4S57A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_0Be_1 : ltac2:(tb__ "0|0|
S0S9S76S57S3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_0Be_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S66S5S45A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_0Be_2 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S45A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_0Be_2 : ltac2:(tb__ "0|0|
S0S9S64S62S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_0Be_2 : ltac2:(tb__ "0|0|
S0S4S7S45S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_0Be_2 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3cA3S4fA3"). Proof. unfold run2_0Be_2; reflexivity. Qed.
Lemma L2_0Be_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS4fSaS2S1dSbS2A1A3A2ScA3S0S4S37U0S4fA2S53A3A2"). Proof. Time (split; [vmr | unfold EfD_0Be_2; reflexivity]). Qed.
Lemma AXD_0Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S65S53S2dA2SeS4S40A2A3"). Proof. Time vmr. Qed.
Lemma HeD_0Be_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S67S40S6bZ2M1A1S1fS40G1A2A3SeG0S56A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_0Be_2 : ltac2:(tb__ "0|1|
S0S9S69S40S6bZ2M0A1S1fS40G0A2S56SaS4S6cG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_0Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S65S5eS2eA2SeS4S58A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_0Be_2 : ltac2:(tb__ "0|0|
S0S9S76S58S3eA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_0Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S25SaS2S20SbS2A1A3A3S3eA3S48A3"). Proof. unfold run3_0Be; reflexivity. Qed.
Lemma L3_0Be : ltac2:(tb__ "0|0|
S1S0S9S1eS48SaS2S25SaS2S20SbS2A1A3A3A2ScA3S1S0S4S37U0S48A2S43A3S0S4S37U1S48A2S5bA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_0Be | unfold Ebg_0Be]; reflexivity]). Qed.
Lemma NX3_0Be : ltac2:(tb__ "0|1|
S1S0S9S64S62S13S5S3eA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_0Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S66S5S43A1S5S3dA1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_0Be : ltac2:(tb__ "0|0|
S0S4S7S43S5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma NX3b_0Be : ltac2:(tb__ "0|0|
S0S9S64S62S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_0Be : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma RUN4_0Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S24SbS2A1A3S3dA3S50A3"). Proof. unfold run4_0Be; reflexivity. Qed.
Lemma L4_0Be : ltac2:(tb__ "0|0|
S1S0S9S1eS50SaS2S24SbS2A1A3A2ScA3S0S4S37U0S50A2S42A3A2"). Proof. Time (split; [vmr | unfold Ems_0Be; reflexivity]). Qed.
Lemma D4_0Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S66S5S42A1S5S38A1A2SeG2S12G0G1S35SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_0Be : ltac2:(tb__ "0|0|
S0S4S7S42S5S38A1A2S38A3"). Proof. vmr. Qed.
Lemma W4_0Be : ltac2:(tb__ "0|1|
S1S0S9S1aS5S38A1M0A1ScA3S1S0S3S13G0A1S13S5S42A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma HeM_0Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S67S38S6eS28S38A1A3SeG0S4aA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_0Be : ltac2:(tb__ "0|0|
S0S9S68S38S6eS28S38A1S4aS74S6S4S8S6fA4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_0Be : ltac2:(tb__ "0|0|
S0S4S6aS28S38A1S6eS32S38S4aA5S4cA3"). Proof. unfold TM0_0Be, TM0_of, RM_0Be; reflexivity. Qed.
Lemma FBM_0Be : ltac2:(tb__ "0|3|
S1S0S9S6dS15S19S13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6dS15S19S13S5S4cA1A1A1G2A3ScA3S0S9S64S62G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETM_0Be : ltac2:(tb__ "0|0|
S0S4S75S4cS17S5S38A1A1A2S46A3"). Proof. vmr. Qed.
Lemma NX5_0Be : ltac2:(tb__ "0|1|
S1S0S9S64S62S13S5S46A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_0Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S23SbS2A1A3S46A3S51A3"). Proof. unfold run5_0Be; reflexivity. Qed.
Lemma L5_0Be : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S23SbS2A1A3A2ScA3S0S4S37U0S51A2S54A3A2"). Proof. Time (split; [vmr | unfold Eq_0Be; reflexivity]). Qed.
Lemma AXQ_0Be : ltac2:(tb__ "0|0|
S0SfS4A1S65S54S33A2SeS4S39A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_0Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S67S39S26S3aA1S29S39S3aA2A3SeG0S4bA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_0Be : ltac2:(tb__ "0|0|
S0S9S68S39S26S3aA1S29S39S3aA2S4bSaS4S2bS3aA1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_0Be : ltac2:(tb__ "0|0|
S0S4S6aS29S39S3aA2S26S3aA1S2bS3aA1S39S4bA5S4dA3"). Proof. unfold TQ0_0Be, TQ0_of, RQ_0Be; reflexivity. Qed.
Lemma FBQ_0Be : ltac2:(tb__ "0|3|
S1S0S9S6dS15S19S13S5S39A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6dS15S19S13S5S4dA1A1A1G2A3ScA3S0S9S64S62G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETQ_0Be : ltac2:(tb__ "0|0|
S0S4S75S4dS17S5S39A1A1A2S47A3"). Proof. vmr. Qed.
Lemma NX6_0Be : ltac2:(tb__ "0|1|
S1S0S9S64S62S13S5S47A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_0Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S22SaS2S27SbS2A1A3A3S47A3S49A3"). Proof. unfold run6_0Be; reflexivity. Qed.
Lemma L6_0Be : ltac2:(tb__ "0|0|
S1S0S9S1eS49SaS2S22SaS2S27SbS2A1A3A3A2ScA3S1S0S4S37U0S49A2S5cA3S0S4S37U1S49A2S60A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_0Be | unfold Xf_0Be]; reflexivity]). Qed.

End F0A_c0Be.

(* [comment removed for export] *)
Module F0A_c0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "sprop_below"; "swf"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "F_typ"; "PostQ1"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf"; "C4_0Bf"; "EQ_0Bf"; "q_0Bf"; "C2_0Bf_1"; "C2_0Bf_2"; "C3_0Bf"; "CD_0Bf"; "ED_0Bf_1"; "ED_0Bf_2"; "P0_0Bf"; "Ems_0Bf"; "Eps_0Bf"; "S1c_0Bf_1"; "S1c_0Bf_2"; "TM_0Bf"; "TQ_0Bf"; "run3_0Bf"; "run6_0Bf"; "RM_0Bf"; "RQ_0Bf"; "TM0_0Bf"; "TQ0_0Bf"; "run2_0Bf_1"; "run2_0Bf_2"; "run4_0Bf"; "run5_0Bf"; "EfD_0Bf_1"; "EfD_0Bf_2"; "Eq_0Bf"; "RD_0Bf_1"; "RD_0Bf_2"; "TDr_0Bf_1"; "TDr_0Bf_2"; "exits1_0Bf"; "run1_0Bf"; "Ebg_0Bf"; "Edr_0Bf"; "TD_0Bf_1"; "TD_0Bf_2"; "W_0Bf"; "Xf_0Bf"; "st_0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_0Bf : list ulink := Wcan 0.
Definition st_0Bf : ustop := UStopLe.
Definition q_0Bf : qvar := QBf.
Definition P0_0Bf : axst := ltac2:(tb__ "0|0|
S31S5fS61S3aA3").

Definition run1_0Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S21SbS2A1A3S41A3").

Definition S1c_0Bf_1 : axst := ltac2:(tb__ "0|0|
S2cS37U0S5aA2S17S5S41A1A1Z1A3").
Definition C2_0Bf_1 : axst := C2_of S1c_0Bf_1.
Definition run2_0Bf_1 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_0Bf_1 : axst := leaf 0 run2_0Bf_1.
Definition ED_0Bf_1 : axst := ED_of EfD_0Bf_1.
Definition RD_0Bf_1 : list sobj := RD_of ED_0Bf_1 1.
Definition TD_0Bf_1 : axst := TD_of ED_0Bf_1 1.
Definition TDr_0Bf_1 : axst := TDr_of TD_0Bf_1.
Definition S1c_0Bf_2 : axst := ltac2:(tb__ "0|0|
S2cS37U0S5aA2S17S5S41A1A1Z2A3").
Definition C2_0Bf_2 : axst := C2_of S1c_0Bf_2.
Definition run2_0Bf_2 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_0Bf_2 : axst := leaf 0 run2_0Bf_2.
Definition ED_0Bf_2 : axst := ED_of EfD_0Bf_2.
Definition RD_0Bf_2 : list sobj := RD_of ED_0Bf_2 2.
Definition TD_0Bf_2 : axst := TD_of ED_0Bf_2 2.
Definition TDr_0Bf_2 : axst := TDr_of TD_0Bf_2.
Definition exits1_0Bf : list axst := ltac2:(tb__ "0|0|
SaS4S44SaS4S45SbS4A1A3A3").

Definition CD_0Bf : axst := CD_of TDr_0Bf_1.
Definition run3_0Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S25SaS2S20SbS2A1A3A3S3eA3").
Definition Eps_0Bf : axst := leaf 0 run3_0Bf.
Definition Ebg_0Bf : axst := leaf 1 run3_0Bf.
Definition C3_0Bf : axst := C3_of Eps_0Bf.
Definition run4_0Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S24SbS2A1A3S3dA3").
Definition Ems_0Bf : axst := leaf 0 run4_0Bf.
Definition C4_0Bf : axst := C4_of Ems_0Bf.
Definition RM_0Bf : list sobj := RM_of C4_0Bf.
Definition TM0_0Bf : axst := TM0_of C4_0Bf.
Definition TM_0Bf : axst := TM_of C4_0Bf.
Definition run5_0Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S23SbS2A1A3S46A3").
Definition Eq_0Bf : axst := leaf 0 run5_0Bf.
Definition EQ_0Bf : axst := EQ_of Eq_0Bf.
Definition RQ_0Bf : list sobj := RQ_of EQ_0Bf q_0Bf.
Definition TQ0_0Bf : axst := TQ0_of EQ_0Bf q_0Bf.
Definition TQ_0Bf : axst := TQ_of EQ_0Bf q_0Bf.
Definition run6_0Bf : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S22SaS2S27SbS2A1A3A3S47A3").
Definition Edr_0Bf : axst := leaf 0 run6_0Bf.
Definition Xf_0Bf : axst := leaf 1 run6_0Bf.

Ltac vmr := vm_compute; reflexivity.
Lemma Cert1_0Bf : ltac2:(tb__ "0|0|
S0S9S72S63S1cSaS2S21SbS2A1A3S62SaS4S41SbS4A1A3S59A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_0Bf exits1_0Bf run1_0Bf); [unfold run1_0Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_0Bf : ltac2:(tb__ "0|2|
S0S9S73S63S1cSaS2S21SbS2A1A3S62SaS70S71S41Z1S1bZ0M0A1M1A3SbS70A1A3S74S4S70S4S71R1G0G1A3LE;S59A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_0Bf 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_0Bf) run1_0Bf); [unfold run1_0Bf, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_0Bf_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S66S5S44A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_0Bf_1 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_0Bf_1 : ltac2:(tb__ "0|0|
S0S9S64S62S13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_0Bf_1 : ltac2:(tb__ "0|0|
S0S4S7S44S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_0Bf_1 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3bA3S4eA3"). Proof. unfold run2_0Bf_1; reflexivity. Qed.
Lemma L2_0Bf_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS4eSaS2S1dSbS2A1A3A2ScA3S0S4S37U0S4eA2S52A3A2"). Proof. Time (split; [vmr | unfold EfD_0Bf_1; reflexivity]). Qed.
Lemma AXD_0Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S65S52S2dA2SeS4S3fA2A3"). Proof. Time vmr. Qed.
Lemma HeD_0Bf_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S67S3fS6bZ1M1A1S1fS3fG1A2A3SeG0S55A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_0Bf_1 : ltac2:(tb__ "0|1|
S0S9S69S3fS6bZ1M0A1S1fS3fG0A2S55SaS4S6cG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_0Bf_1 : ltac2:(tb__ "0|0|
S0SfS4A1S65S5dS2eA2SeS4S57A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_0Bf_1 : ltac2:(tb__ "0|0|
S0S9S76S57S3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_0Bf_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S66S5S45A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S2fS30A4SbG0A1A3S2aA4A2A3"). Proof. Time vmr. Qed.
Lemma W2_0Bf_2 : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S45A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_0Bf_2 : ltac2:(tb__ "0|0|
S0S9S64S62S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_0Bf_2 : ltac2:(tb__ "0|0|
S0S4S7S45S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_0Bf_2 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3cA3S4fA3"). Proof. unfold run2_0Bf_2; reflexivity. Qed.
Lemma L2_0Bf_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS4fSaS2S1dSbS2A1A3A2ScA3S0S4S37U0S4fA2S53A3A2"). Proof. Time (split; [vmr | unfold EfD_0Bf_2; reflexivity]). Qed.
Lemma AXD_0Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S65S53S2dA2SeS4S40A2A3"). Proof. Time vmr. Qed.
Lemma HeD_0Bf_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S67S40S6bZ2M1A1S1fS40G1A2A3SeG0S56A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_0Bf_2 : ltac2:(tb__ "0|1|
S0S9S69S40S6bZ2M0A1S1fS40G0A2S56SaS4S6cG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_0Bf_2 : ltac2:(tb__ "0|0|
S0SfS4A1S65S5eS2eA2SeS4S58A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_0Bf_2 : ltac2:(tb__ "0|0|
S0S9S76S58S3eA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_0Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S25SaS2S20SbS2A1A3A3S3eA3S48A3"). Proof. unfold run3_0Bf; reflexivity. Qed.
Lemma L3_0Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS48SaS2S25SaS2S20SbS2A1A3A3A2ScA3S1S0S4S37U0S48A2S43A3S0S4S37U1S48A2S5bA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_0Bf | unfold Ebg_0Bf]; reflexivity]). Qed.
Lemma NX3_0Bf : ltac2:(tb__ "0|1|
S1S0S9S64S62S13S5S3eA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_0Bf : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S66S5S43A1S5S3dA1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_0Bf : ltac2:(tb__ "0|0|
S0S4S7S43S5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma NX3b_0Bf : ltac2:(tb__ "0|0|
S0S9S64S62S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_0Bf : ltac2:(tb__ "0|1|
S1S0S9S1aS5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma RUN4_0Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S24SbS2A1A3S3dA3S50A3"). Proof. unfold run4_0Bf; reflexivity. Qed.
Lemma L4_0Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS50SaS2S24SbS2A1A3A2ScA3S0S4S37U0S50A2S42A3A2"). Proof. Time (split; [vmr | unfold Ems_0Bf; reflexivity]). Qed.
Lemma D4_0Bf : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S66S5S42A1S5S38A1A2SeG2S12G0G1S35SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_0Bf : ltac2:(tb__ "0|0|
S0S4S7S42S5S38A1A2S38A3"). Proof. vmr. Qed.
Lemma W4_0Bf : ltac2:(tb__ "0|1|
S1S0S9S1aS5S38A1M0A1ScA3S1S0S3S13G0A1S13S5S42A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma HeM_0Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S67S38S6eS28S38A1A3SeG0S4aA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_0Bf : ltac2:(tb__ "0|0|
S0S9S68S38S6eS28S38A1S4aS74S6S4S8S6fA4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_0Bf : ltac2:(tb__ "0|0|
S0S4S6aS28S38A1S6eS32S38S4aA5S4cA3"). Proof. unfold TM0_0Bf, TM0_of, RM_0Bf; reflexivity. Qed.
Lemma FBM_0Bf : ltac2:(tb__ "0|3|
S1S0S9S6dS15S19S13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6dS15S19S13S5S4cA1A1A1G2A3ScA3S0S9S64S62G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETM_0Bf : ltac2:(tb__ "0|0|
S0S4S75S4cS17S5S38A1A1A2S46A3"). Proof. vmr. Qed.
Lemma NX5_0Bf : ltac2:(tb__ "0|1|
S1S0S9S64S62S13S5S46A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_0Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S23SbS2A1A3S46A3S51A3"). Proof. unfold run5_0Bf; reflexivity. Qed.
Lemma L5_0Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S23SbS2A1A3A2ScA3S0S4S37U0S51A2S54A3A2"). Proof. Time (split; [vmr | unfold Eq_0Bf; reflexivity]). Qed.
Lemma AXQ_0Bf : ltac2:(tb__ "0|0|
S0SfS4A1S65S54S33A2SeS4S39A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_0Bf : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S67S39S26S3aA1S29S39S3aA2A3SeG0S4bA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_0Bf : ltac2:(tb__ "0|0|
S0S9S68S39S26S3aA1S29S39S3aA2S4bSaS4S2bS3aA1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_0Bf : ltac2:(tb__ "0|0|
S0S4S6aS29S39S3aA2S26S3aA1S2bS3aA1S39S4bA5S4dA3"). Proof. unfold TQ0_0Bf, TQ0_of, RQ_0Bf; reflexivity. Qed.
Lemma FBQ_0Bf : ltac2:(tb__ "0|3|
S1S0S9S6dS15S19S13S5S39A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S6dS15S19S13S5S4dA1A1A1G2A3ScA3S0S9S64S62G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETQ_0Bf : ltac2:(tb__ "0|0|
S0S4S75S4dS17S5S39A1A1A2S47A3"). Proof. vmr. Qed.
Lemma NX6_0Bf : ltac2:(tb__ "0|1|
S1S0S9S64S62S13S5S47A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_0Bf : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S22SaS2S27SbS2A1A3A3S47A3S49A3"). Proof. unfold run6_0Bf; reflexivity. Qed.
Lemma L6_0Bf : ltac2:(tb__ "0|0|
S1S0S9S1eS49SaS2S22SaS2S27SbS2A1A3A3A2ScA3S1S0S4S37U0S49A2S5cA3S0S4S37U1S49A2S60A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_0Bf | unfold Xf_0Bf]; reflexivity]). Qed.

End F0A_c0Bf.

