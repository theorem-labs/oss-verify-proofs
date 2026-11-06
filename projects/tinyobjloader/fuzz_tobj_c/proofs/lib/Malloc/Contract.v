(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "app"; "pair"; "prod"; "false"; "None"; "true"; "bool"; "nat"; "option"; "Some"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "sv"; "valuation"; "SVar"; "SLit"; "rw"; "FcsrFrm0"; "mkSS"; "sstate"; "rm"; "SPUle"; "DUnknown"; "cell"; "mkObj"; "SAlu"; "SPBranch"; "SPAlign"; "SPNot"; "image_byte"; "obj_range"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "VmMaps"; "with_vmmaps"; "m_vmmaps"; "vm_forget_range"; "with_vm_backing"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_blocks"; "ma_L"; "ma_s"; "ma_owned"; "MInv"; "layout_extends"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "pre_regs"; "segsP"; "segsU"; "setregs"; "cut_regs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "opp"; "mul"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.WithSegs"; "F_sp_aligned"; "stack_win"; "F_depth"; "F_sp_high"; "MInvR"; "client_addr"; "mem_kept"; "vm_insensitive"; "NPOSTM"; "V_DEPTH"; "V_RES"; "errno_range"; "tp_ok"; "F_top"; "ec_free"; "V_TOP"; "alloc_static"; "ec_calloc"; "ec_malloc"; "ec_ret_free"; "top_high"; "top_var"; "wseg_addr"; "EC"; "ec_ret_calloc"; "ec_ret_calloc2"; "ec_ret_memset"; "ec_ret_null"; "ec_ret_ok"; "mem_kept_owned"; "rd_of"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "calloc_stack"; "malloc_stack"; "free_stack"; "topL"; "C_P"; "C_U"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctx"; "mc_errno"; "mc_libc"; "mc_lock"; "mc_replaced"; "mc_tp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "st_init_done"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "EC_U"; "L_free_null"; "Pre_free_null"; "calloc_contract"; "calloc_contract_ex"; "free_contract"; "free_contract_ex"; "malloc_contract"; "malloc_contract_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.WithSegs.Contracts"; "init_kept"; "J_alloc_pre"; "ok_sideK"; "F_res_facts"; "JL_free"; "JL_malloc_null"; "J_free_pre"; "L_calloc_null"; "L_calloc_ok"; "L_free"; "L_free_null"; "Posts_calloc"; "Posts_malloc"; "Pre_calloc"; "Pre_free"; "Pre_free_null"; "Pre_malloc"; "V_FREE_A1"; "block_obj"; "calloc_size"; "JL_calloc_ok"; "JL_malloc_ok"; "L_malloc_null"; "L_malloc_ok"; "client_addr_not_owned_stmt"; "top_kept"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "LQ"; "SP"; "ok_frame"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "BC_EQ"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_writable"; "@Corelib.Lists.ListDef";
"Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "find_segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "CTX_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymFrame SymSummary SymCall SymComplete ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocCalloc MallocIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import ZEval.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition wseg_addr (a : word) : bool := ltac2:(tb__ "0|0|
SbSacA1S9Lx;SafVsegs;S45Q40Va;A2Z1A3SacSadR1A1Lseg;S6Xbx2").

Definition rd_of (m : word -> option byte) : word -> option byte := ltac2:(tb__ "0|2|
S46Q40A1SbS46Q8A1M0A1M1G1Lx;Vm;R1A1G0ScG0R1A2Lb;S22Vsegs;R1A2Xbx2La;").

Definition wok_of (m : word -> option byte) : word -> bool := ltac2:(tb__ "0|1|
S46Q40A1SbS46Q8A1M0A1S9Lx;Vm;R1A1G0S8Lb;S5eR1A1Xbx2La;").

Definition tp_ok (C : mconsts) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S25S29S45Q40S15Vrho;P18A2A2S77VC;A1A3").

Definition MInvR (C : mconsts) (A : MA) (rho : valuation) (md : Model) : Prop := ltac2:(tb__ "0|1|
S36VC;VA;S66S19Vrho;A1M0A1S67G0A1S2eVmd;A1A5").

Definition errno_range (C : mconsts) (a : Z) : Prop := ltac2:(tb__ "0|1|
S24S40S73VC;A1M0Va;A2S41Va;S3fG0Z4A2A2A2").

Definition alloc_static (C : mconsts) (a : Z) : Prop := ltac2:(tb__ "0|5|
S28S24S40S74VC;A1M0Va;A2S41Va;S3fG0Z38A2A2A2S28S24S40S71VC;A1M1Va;A2S41Va;S3fG1Z8M2A2A2A2S28S24S40S70VC;A1M3Va;A2S41Va;S3fG3G2A2A2A2S24S40S76VC;A1M4Va;A2S41Va;S3fG4Z4A2A2A2A2A2A2").

Definition mem_kept_owned (C : mconsts) (A A' : MA) (m0 m1 : word -> option byte) : Prop := ltac2:(tb__ "0|1|
S29S24S40Z0R1A2S41R1S42Z2Z40A2A2A2S27S35VC;VA;R2A3A1S27S35VC;VA';R3A3A1S27S53VC;R4A2A1S27S58VC;R5A2A1S25SbS46Q8A1A1Vm1;S47Q40R6A2M0A1Vm0;G0A1A3F_;F_;F_;F_;F_;Fa;").

Definition client_addr (C : mconsts) (A : MA) (a : Z) : Prop := ltac2:(tb__ "0|2|
S28S40S6dS33VA;A1A1Va;A2S28S26S29S29S26S29S29S24Sa5S5S29S29A2S4S29S29R2R1A4S32VA;A1A3S24S40R2Va;A2S41Va;S3fR2R1A2A2A2A2Ln;A2Lb;A2S24S25S9S5eS47Q40Va;A2A1S8A3S24S27S24S40S72VC;A1M0Va;A2S41Va;S3fG0Sb1A2A2A2A1S24S27S24S40S75VC;A1M1Va;A2S41Va;S3fG1Z4A2A2A2A1S27S53VC;Va;A2A1A2A2A2A2A2").

Definition mem_kept (C : mconsts) (A A' : MA) (m0 m1 : word -> option byte) : Prop := ltac2:(tb__ "0|1|
S29S24S40Z0R1A2S41R1S42Z2Z40A2A2A2S4dVC;VA;R2A3S4dVC;VA';R3A3S27S53VC;R4A2A1S27S58VC;R5A2A1S25SbS46Q8A1A1Vm1;S47Q40R6A2M0A1Vm0;G0A1A3F_;F_;F_;F_;F_;Fa;").

Definition vm_insensitive (Kc : list event -> Model -> Prop) : Prop := ltac2:(tb__ "0|2|
S24S2S2bA1M0S2aS2cVKc;R3R2A2VKc;R4S2dR2R3A2A2F_;Fvm;Fmd;Ftr;G0S2aS2S5S46Q40A1M1G1A2A1S2G1A1VKc;R4R3A2VKc;R5S30R3R2R4A3A2F_;Fmt;Flz;Fmd;Ftr;A2").

Lemma vm_insensitive_maps Kc : ltac2:(tb__ "0|0|
S4fVKc;A1S2S2bA1S2aS2cVKc;R3R2A2VKc;R4S2dR2R3A2A2F_;Fvm;Fmd;Ftr;F_;").
Proof using . intros [H _]. exact H. Qed.
Lemma vm_insensitive_forget Kc : ltac2:(tb__ "0|0|
S4fVKc;A1S2S2bA1S2aS29S29VKc;R4R3A2VKc;R5S2fR3R2R4A3A2F_;Fhi;Flo;Fmd;Ftr;F_;").
Proof using . intros [_ H] tr md lo hi HK. unfold vm_forget_range. apply H. exact HK. Qed.

Definition V_RES : positive := 110%positive.
Definition NPOSTM : positive := 140%positive.

Definition V_DEPTH : positive := 15%positive.
Definition stack_win (depth : Z) : sobj := ltac2:(tb__ "0|0|
S1dS13PaA1S13S51A1S14Z0A1S1S1cA1S1bA5").
Definition F_depth (depth : Z) : list sprop := ltac2:(tb__ "0|1|
S0SfS1fSaaS14S43Vdepth;A1A1S13S51A1M0A3S0SfS1fSaaG0S14S43S42Z2Z28A2A1A1A3S1SfA1A3A3").

Definition F_sp_aligned : sprop := SPAlign 10%positive 4.

Definition F_sp_high (depth : Z) : sprop := ltac2:(tb__ "0|0|
S1aS14Z7fff7f800000A1S1eSa9S13PaA1S13S51A1A3A2").

Definition V_TOP : positive := 30%positive.
Definition F_top : list sprop := ltac2:(tb__ "0|1|
S0SfS1aS13S57A1M0S1eSa9S13PaA1S13S51A1A3A2S0SfS1aS14Z7fff7f800000A1G0A2S0SfS1aG0S14Z7fffff800000A1A2S1SfA1A3A3A3").

Definition top_high (A : MA) (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S40S6dS33VA;A1A1S3fS45Q40M0S15Vrho;PaA2A2Sb2Z40S45G0S15Vrho;S51A2A2A2A2A2").
Definition top_var (A : MA) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S25S29S45Q40S15Vrho;S57A2A2S6dS33VA;A1A1A3").

Record entry_consts := EC {
  ec_malloc : Z; ec_calloc : Z; ec_free : Z;
  ec_ret_null : Z;
  ec_ret_ok : Z;
  ec_ret_calloc : Z;
  ec_ret_free : Z;
  ec_ret_calloc2 : Z;
  ec_ret_memset : Z
}.
Definition EC_P : entry_consts := EC 0x1fe2c 0x1fbb4 0x1fcec 0x20814 0x2151c 0x1fbf4 0x1fff8 0x1fcd8 0x2708c.
Definition EC_U : entry_consts := ltac2:(tb__ "0|1|
S5fS3fZ1fe2cZ740M0A2S3fZ1fbb4G0A2S3fZ1fcecG0A2S3fZ20814G0A2S3fZ2151cG0A2S3fZ1fbf4G0A2S3fZ1fff8G0A2S3fZ1fcd8G0A2S3fZ2708cG0A2A9").

Section Contracts.
Variable C : mconsts.
Variable E : entry_consts.

Definition Pre_malloc : sstate := ltac2:(tb__ "0|0|
S17S5aVE;A1S3aS39S16S7S11A1S0S10S49S6bA1S1S10A1A3S3SfS0SfS48S0SfS4bS6bA1S1SfA1A3A3S3SfS4aS6bA1S55A3A3S38S6A9").

Definition Pre_mallocI : sstate := ltac2:(tb__ "0|0|
S17S5aVE;A1S3aS39S16S7S11A1S0S10S49S6bA1S1S10A1A3S3SfS0SfS48S0SfS4bS6bA1S1SfA1A3A3S4aS6bA1A3S38S6A9").

Definition block_obj (size : sv) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S1dS13S52A1S14Z0A1Vsize;S1S1cA1Vd;A5").

Definition F_res_facts (size : sv) : list sprop := ltac2:(tb__ "0|1|
S0SfS20S52Z4A2S0SfS21S1fSabS13S52A1M0S14Z0A1A3A1S0SfS1aS14Z1000A1G0A2S0SfS1aS1eSa9G0Vsize;A3S14Z7fffff800000A1A2S1SfA1A3A3A3A3").

Definition L_malloc_null : sstate := ltac2:(tb__ "0|1|
S17S63VE;A1S3dS3eS38A1S0S5SaS11A2M0S4SaS11UaS14Z0A1A4S1G0A1A3A2S39S16S7S11A1S0S10S49S6bA1S1S10A1A3S3SfS0SfS48S0SfS4bS6bA1S1SfA1A3A3S4aS6bA1A3S50S6A9").

Definition L_malloc_ok : sstate := ltac2:(tb__ "0|1|
S17S64VE;A1S3eS38A1S39S16S7S11A1S0S10S49S6bA1S0S10S99S13PcA1M0S1bA2S1S10A1A3A3S3SfS8aG0A1S3SfS0SfS48S0SfS4bS6bA1S1SfA1A3A3S4aS6bA1A3A3S50S6A9").

Definition J_alloc_pre (A : MA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|0|
S12S2S2bA1S2aS24S4cVC;VA;R3R1A4S24VKc;R2R1A2S24S54VC;R3A2S24S25S9S7cS34VA;A1A1S8A3S5dVA;R3A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition J_alloc_preT (A : MA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|0|
S12S2S2bA1S2aS24S4cVC;VA;R3R1A4S24VKc;R2R1A2S24S54VC;R3A2S24S25S9S7cS34VA;A1A1S8A3S5cVA;R3A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition top_kept (A A' : MA) : Prop := ltac2:(tb__ "0|0|
S25S29S6dS33VA';A1A1S6dS33VA;A1A1A3").
Definition init_kept (A A' : MA) : Prop := ltac2:(tb__ "0|0|
S24S25S9S7cS34VA;A1A1S8A3S25S9S7cS34VA';A1A1S8A3F_;Sa0VA;VA';A2A2").
Lemma init_kept_init A A' : ltac2:(tb__ "0|0|
S87VA;VA';A2S25S9S7cS34VA;A1A1S8A3S25S9S7cS34VA';A1A1S8A3F_;F_;").
Proof. intros [H _]. exact H. Qed.
Lemma init_kept_top A A' : ltac2:(tb__ "0|0|
S87VA;VA';A2S25S29S6dS33VA';A1A1S6dS33VA;A1A1A3F_;").
Proof. intros [_ H]. exact H. Qed.
Lemma init_kept_extends A A' n : ltac2:(tb__ "0|0|
S37S33VA;A1S33VA';A1Vn;A3S25S9S7cS34VA';A1A1S8A3S87VA;VA';A2F_;F_;").
Proof. intros HE Hi. split; [intros _; exact Hi | exact (layout_extends_top _ _ _ HE)]. Qed.

Definition JL_malloc_null (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|0|
S12S12S2S2bA1S2aS26S31S31S24S4cVC;R1R4R2A4S24S25S2S5S29S29A2A1S32R1A1S32VA;A1A3S24S4eVC;VA;R1S19R5A1S19R4A1A5S24S87VA;R1A2VKc;R3R2A2A2A2A2A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition JL_malloc_ok (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|3|
S12S12S2S2bA1S2aS26S31S31S26S2S5S29S29A2M0A1M1G1S26G1G1S24S4cVC;R3R6R4A4S24S25G1S32R3A1S3G0R2S0G0S4S29S29S45Q40M2S15R6S52A2A2S45G2S15R7PcA2A2A4R1A3A3A3S24S25G1S32VA;A1S3G0R2R1A3A3S24S4eVC;VA;R3S19R7A1S19R6A1A5S24S87VA;R3A2VKc;R5R4A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition Posts_malloc (A : MA) Kc : list (sstate * jpost) := ltac2:(tb__ "0|1|
S0S5S18S68A2M0S4S18S68S9dS8cVA;VKc;A2A4S0G0S4S18S68S9eS9cVA;VKc;A2A4S1G0A1A3A3").

Definition ok_sideK (ok : world -> Prop) (Kc : list event -> Model -> Prop) : Prop := ltac2:(tb__ "0|0|
S24Sa4Vsegs;Vok;VKc;A3S24Sb0Vsegs;Vok;VKc;A3S4fVKc;A1A2A2").

Definition malloc_contract : Prop := ltac2:(tb__ "0|0|
Sa8OF_;S31S2S2bA1S2aOF_;F_;S12S89R4R2A2Sa7Vsegs;R5Sa1Vsegs;S88R4R3A2S97R2A4S69Vsegs;S38R2S93R4R3A2A4A4F_;Frho;FKc;FA;Fok;").

Definition Pre_calloc : sstate := ltac2:(tb__ "0|0|
S17S59VE;A1S3aS39S16S7S11A1S0S10S49S6aA1S1S10A1A3S3SfS0SfS48S0SfS4bS6aA1S1SfA1A3A3S3SfS4aS6aA1S55A3A3S38S6A9").
Definition Pre_callocI : sstate := ltac2:(tb__ "0|0|
S17S59VE;A1S3aS39S16S7S11A1S0S10S49S6aA1S1S10A1A3S3SfS0SfS48S0SfS4bS6aA1S1SfA1A3A3S4aS6aA1A3S38S6A9").

Definition calloc_size : sv := SMd M_MUL (SVar 12) (SVar 13).

Definition L_calloc_null (pc : Z) : sstate := ltac2:(tb__ "0|1|
S17Vpc;S3dS3eS38A1S0S5SaS11A2M0S4SaS11UaS14Z0A1A4S1G0A1A3A2S39S16S7S11A1S0S10S49S6aA1S1S10A1A3S3SfS0SfS48S0SfS4bS6aA1S1SfA1A3A3S4aS6aA1A3S50S6A9").
Definition L_calloc_ok (pc : Z) : sstate := ltac2:(tb__ "0|0|
S17Vpc;S3eS38A1S39S16S7S11A1S0S10S49S6aA1S0S10S99S9aS1bA2S1S10A1A3A3S3SfS8aS9aA1S3SfS0SfS48S0SfS4bS6aA1S1SfA1A3A3S4aS6aA1A3A3S50S6A9").

Definition JL_calloc_ok (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|3|
S12S12S2S2bA1S2aS26S31S31S26S2S5S29S29A2M0A1M1G1S26G1G1S24S4cVC;R3R6R4A4S24S25G1S32R3A1S3G0R2S0G0S4S29S29S45Q40M2S15R6S52A2A2S44S45G2S15R7PcA2A2S45G2S15R7PdA2A2A2A4R1A3A3A3S24S25G1S32VA;A1S3G0R2R1A3A3S24S4eVC;VA;R3S19R7A1S19R6A1A5S24S87VA;R3A2VKc;R5R4A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition Posts_calloc (A : MA) Kc : list (sstate * jpost) := ltac2:(tb__ "0|4|
S0S5S18S68A2M0S4S18S68S8eS60VE;A1M1A1S8cVA;VKc;A2M2A4S0G0S4S18S68S8eS61VE;A1A1G2A4S0G0S4S18S68S8fG1A1S9bVA;VKc;A2M3A4S0G0S4S18S68S8fS62VE;A1A1G3A4S1G0A1A3A3A3A3").

Definition calloc_contract : Prop := ltac2:(tb__ "0|0|
Sa8OF_;S31S2S2bA1S2aOF_;F_;S12S89R4R2A2Sa7Vsegs;R5Sa1Vsegs;S88R4R3A2S94R2A4S69Vsegs;S38R2S92R4R3A2A4A4F_;Frho;FKc;FA;Fok;").

Definition V_FREE_A1 : positive := 16%positive.
Definition Pre_free : sstate := ltac2:(tb__ "0|1|
S17S56VE;A1S3dS3aS0S5SaS11A2M0S4SaS11UbS13S98A1A4S1G0A1A3A2S39S16S7S11A1S0S10S49S6cA1S0S10S1dS13PcA1S14Z0A1S13PdA1S1S1cA1S1bA5S1S10A1A3A3S3SfS0SfS48S0SfS4bS6cA1S1SfA1A3A3S3SfS4aS6cA1S55A3A3S38S6A9").
Definition Pre_freeI : sstate := ltac2:(tb__ "0|1|
S17S56VE;A1S3dS3aS0S5SaS11A2M0S4SaS11UbS13S98A1A4S1G0A1A3A2S39S16S7S11A1S0S10S49S6cA1S0S10S1dS13PcA1S14Z0A1S13PdA1S1S1cA1S1bA5S1S10A1A3A3S3SfS0SfS48S0SfS4bS6cA1S1SfA1A3A3S4aS6cA1A3S38S6A9").

Definition L_free : sstate := ltac2:(tb__ "0|0|
S17S5bVE;A1S3eS38A1S39S16S7S11A1S0S10S49S6cA1S1S10A1A3S3SfS0SfS48S0SfS4bS6cA1S1SfA1A3A3S4aS6cA1A3S50S6A9").

Definition J_free_pre (A : MA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|1|
S12S2S2bA1S2aS24S4cVC;VA;R3R1A4S24Sa5S5S29S29A2S4S29S29S45Q40M0S15R3PcA2A2S45G0S15R3PdA2A2A4S32VA;A1A3S24VKc;R2R1A2S24S54VC;R3A2S24S25S9S7cS34VA;A1A1S8A3S5dVA;R3A2A2A2A2A2A2Lmd;Ltr;Lrho;").
Definition J_free_preT (A : MA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|1|
S12S2S2bA1S2aS24S4cVC;VA;R3R1A4S24Sa5S5S29S29A2S4S29S29S45Q40M0S15R3PcA2A2S45G0S15R3PdA2A2A4S32VA;A1A3S24VKc;R2R1A2S24S54VC;R3A2S24S25S9S7cS34VA;A1A1S8A3S5cVA;R3A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Definition JL_free (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|3|
S12S12S2S2bA1S2aS26S31S31S26S2S5S29S29A2M0A1M1G1S26G1G1S24S4cVC;R3R6R4A4S24S25G1S32VA;A1S3G0R2S0G0S4S29S29S45Q40M2S15R7PcA2A2S45G2S15R7PdA2A2A4R1A3A3A3S24S25G1S32R3A1S3G0R2R1A3A3S24S4eVC;VA;R3S19R7A1S19R6A1A5S24S87VA;R3A2VKc;R5R4A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition free_contract : Prop := ltac2:(tb__ "0|1|
Sa8OF_;S31S2S2bA1S2aOF_;F_;S12S89R4R2A2Sa7Vsegs;R5Sa1Vsegs;S8dR4R3A2S95R2A4S69Vsegs;S38R2S0S5S18S68A2M0S4S18S68S90S8bR4R3A2A4S1G0A1A3A4A4F_;Frho;FKc;FA;Fok;").

Definition Pre_free_null : sstate := ltac2:(tb__ "0|2|
S17S56VE;A1S3dS3aS0S5SaS11A2M0S4SaS11UaS14Z0M1A1A4S1G0A1A3A2S39S16S7S11A1S0S10S49G1A1S1S10A1A3S0SfS48S1SfA1A3S38S6A9").
Definition L_free_null : sstate := ltac2:(tb__ "0|2|
S17S5bVE;A1S3dS3aS0S5SaS11A2M0S4SaS11UaS14Z0M1A1A4S1G0A1A3A2S39S16S7S11A1S0S10S49G1A1S1S10A1A3S0SfS48S1SfA1A3S38S6A9").

Definition free_null_contract : Prop := ltac2:(tb__ "0|0|
Sa8OF_;S2S2bA1S2aOF_;F_;S12Sa4Vsegs;R3R2A3Sa7Vsegs;R4Sa3Vsegs;R3S96R2A4Sa2Vsegs;R3S38R2S0S78S7aS91S79A2S1S78A1A3A5A4F_;Frho;FK;Fok;").

Definition objs_client_ok (A : MA) (rho : valuation) (R : list sobj) : Prop := ltac2:(tb__ "0|0|
SaeS10S10S23Vrho;R1A2S5S29S29A2S29S24S40SdS29S29R2A3R1A2S41R1SeS29S29R2A3A2A2S24S27S35VC;VA;R2A3A1S27S53VC;R2A2A1A2F_;Fa;Tr;Lo;VR;A3").

Definition client_addr_not_owned_stmt : Prop := ltac2:(tb__ "0|0|
S31S12S2aS29S4cVC;R4R3R2A4S4dVC;R5R2A3S27S35VC;R6R3A3A1F_;F_;Fa;Fmd;Frho;FA;").

Lemma mem_kept_weaken : ltac2:(tb__ "0|1|
S31S31S12S2aS12S2aS46Q40A1SbS46Q8A1A1F_;M0G0S9fS4cVC;R9R7R6A4S4cVC;R9R6R5A4S65VC;RbRaR5R4A5S4eVC;RcRbR6R5A5F_;F_;F_;F_;Fm1;Fm0;Fmd';Frho';Fmd;Frho;FA';FA;").
Proof using .
  intros A A' rho md rho' md' m0 m1 Hn HM HM' Hk a Ha Hc Hc' He Hs.
  exact (Hk a Ha (Hn A rho md a HM Hc) (Hn A' rho' md' a HM' Hc') He Hs).
Qed.

Lemma mem_kept_trans : ltac2:(tb__ "0|2|
S31S31S31S46Q40A1SbS46Q8A1A1F_;M0G0G0S29S4dVC;R7R1A3S4dVC;R6R2A3S4dVC;R8R3A3F_;F_;Fa;S4eVC;R7R6R4R3A5M1G1S4eVC;R9R7R6R4A5F_;F_;F_;Fm3;Fm2;Fm1;FA3;FA2;FA1;").
Proof using .
  intros A1 A2 A3 m1 m2 m3 Hmid H12 H23 a Ha H1 H3 He Hs.
  rewrite (H23 a Ha (Hmid a H1 H3) H3 He Hs). exact (H12 a Ha H1 (Hmid a H1 H3) He Hs).
Qed.

Lemma client_addr_blocks_mono : ltac2:(tb__ "0|2|
S31S31S29S25S29S6dS33R2A1A1S6dS33R3A1A1A3S5S29S29A2M0Sa5G0R1S32R5A1M1A3Sa5G0R2G1A3F_;Fb;S4dVC;R5R3A3S4dVC;R5R4A3F_;F_;F_;Fa;FB;FA;").
Proof using .
  intros A B a HT Hsub [H|[(b & n & Hin & Hr)|H]]; [left; rewrite HT; exact H | | right; right; exact H].
  right; left. exists b, n. split; [exact (Hsub _ Hin) | exact Hr].
Qed.

Definition malloc_contract_ex : Prop := ltac2:(tb__ "0|0|
S31S2S2bA1S2aOF_;F_;S12S4fR2A1Sa6Vsegs;Sa1Vsegs;S88R4R3A2S97R2A4S69Vsegs;S38R2S93R4R3A2A4A3F_;Frho;FKc;FA;").

Definition calloc_contract_ex : Prop := ltac2:(tb__ "0|0|
S31S2S2bA1S2aOF_;F_;S12S4fR2A1Sa6Vsegs;Sa1Vsegs;S88R4R3A2S94R2A4S69Vsegs;S38R2S92R4R3A2A4A3F_;Frho;FKc;FA;").

Definition free_contract_ex : Prop := ltac2:(tb__ "0|1|
S31S2S2bA1S2aOF_;F_;S12S4fR2A1Sa6Vsegs;Sa1Vsegs;S8dR4R3A2S95R2A4S69Vsegs;S38R2S0S5S18S68A2M0S4S18S68S90S8bR4R3A2A4S1G0A1A3A4A3F_;Frho;FKc;FA;").

Definition free_null_contract_ex : Prop := ltac2:(tb__ "0|0|
S2S2bA1S2aOF_;F_;S12Sa6Vsegs;Sa3Vsegs;R2S96R1A4Sa2Vsegs;R2S38R1S0S78S7aS91S79A2S1S78A1A3A5A3Frho;FK;").

End Contracts.
End WithSegs.

Definition malloc_contract_P : Prop := ltac2:(tb__ "0|0|
S85S3bS6eS7dA3").
Definition calloc_contract_P : Prop := ltac2:(tb__ "0|0|
S81S3bS6eS7dA3").
Definition free_contract_P   : Prop := ltac2:(tb__ "0|0|
S83S3bS6eS7dA3").
Definition malloc_contract_U : Prop := ltac2:(tb__ "0|0|
S85S3cS6fS7eA3").
Definition calloc_contract_U : Prop := ltac2:(tb__ "0|0|
S81S3cS6fS7eA3").
Definition free_contract_U   : Prop := ltac2:(tb__ "0|0|
S83S3cS6fS7eA3").
Definition malloc_contract_ex_P : Prop := ltac2:(tb__ "0|0|
S86S3bS6eS7dA3").
Definition calloc_contract_ex_P : Prop := ltac2:(tb__ "0|0|
S82S3bS6eS7dA3").
Definition free_contract_ex_P   : Prop := ltac2:(tb__ "0|0|
S84S3bS6eS7dA3").
Definition free_null_contract_ex_P : Prop := free_null_contract_ex segsP EC_P.
Definition malloc_contract_ex_U : Prop := ltac2:(tb__ "0|0|
S86S3cS6fS7eA3").
Definition calloc_contract_ex_U : Prop := ltac2:(tb__ "0|0|
S82S3cS6fS7eA3").
Definition free_contract_ex_U   : Prop := ltac2:(tb__ "0|0|
S84S3cS6fS7eA3").
Definition free_null_contract_ex_U : Prop := free_null_contract_ex segsU EC_U.

Lemma run_free_null_P : ltac2:(tb__ "0|1|
S25SbS2S78A1M0A1S7bS3bUaS1S29A1S80S7dA1S8A5ScG0S0S78S7aS7fS7dA1S79A2S1S78A1A3A2A3").
Proof. vm_compute. reflexivity. Qed.
Lemma run_free_null_U : ltac2:(tb__ "0|1|
S25SbS2S78A1M0A1S7bS3cUaS1S29A1S80S7eA1S8A5ScG0S0S78S7aS7fS7eA1S79A2S1S78A1A3A2A3").
Proof. vm_compute. reflexivity. Qed.

Theorem free_null_contract_P : free_null_contract segsP EC_P.
Proof.
  intros ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsP 10 [] (Pre_free_null EC_P) _ ok K rho eq_refl run_free_null_P Hok).
Qed.

Theorem free_null_contract_U : free_null_contract segsU EC_U.
Proof.
  intros ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsU 10 [] (Pre_free_null EC_U) _ ok K rho eq_refl run_free_null_U Hok).
Qed.

Theorem free_null_contract_ex_P_proof : free_null_contract_ex_P.
Proof.
  intros K rho w Hsp.
  destruct (sym_run_complete segsP 10 [] (Pre_free_null EC_P) _ K rho w eq_refl run_free_null_P Hsp) as (L & rho' & w' & HinL & Hst & Hag & HL).
  exists w'. split; [exact Hst|]. exists L, rho'. auto.
Qed.

Theorem free_null_contract_ex_U_proof : free_null_contract_ex_U.
Proof.
  intros K rho w Hsp.
  destruct (sym_run_complete segsU 10 [] (Pre_free_null EC_U) _ K rho w eq_refl run_free_null_U Hsp) as (L & rho' & w' & HinL & Hst & Hag & HL).
  exists w'. split; [exact Hst|]. exists L, rho'. auto.
Qed.
