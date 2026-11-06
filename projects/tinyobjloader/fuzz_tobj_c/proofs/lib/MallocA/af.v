(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.

(* [comment removed for export] *)
Module F0A_cls.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "sv"; "SPUlt"; "SVar"; "SAlu"; "SPAlign"; "FcsrFrm0"; "SPBranch"; "SPEq"; "SPNot"; "mkSS"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "app"; "list"; "nat"; "nil"; "pair"; "prod"; "true"; "None"; "false"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "modulo"; "pow"; "sub"; "lt"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "vN8"; "qvar"; "vN8g"; "FACTS"; "F_cas"; "OBJS0"; "P0_f"; "VFACT"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "LOW_SHADOW_BEG"; "IMG_HI"; "HIGH_SHADOW_END"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "FACTSc"; "F_pc"; "blk_cls"; "cls_hyp"; "P0_fc"; "blk_geo"; "cls_geo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "AE_A"; "V_FREE_A1"; "ae_free"; "free_depth"; "mkA"; "pre_facts"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "F_geom_fn"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@Stdlib.Lists.List"; "hd"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition blk_cls (p n : Z) : Prop := ltac2:(tb__ "0|0|
S29S19S18Vp;Vn;A2S2fA2S19S2eS1cVp;Z10A2A2A2").

Definition cls_hyp (hi : bool) (p n : Z) : Prop := ltac2:(tb__ "0|0|
SeOLhi;Vhi;S19S2eS1cVp;Z10A2A2S19S18Vp;Vn;A2S2fA2Xex2").
Lemma cls_hyp_blk : ltac2:(tb__ "0|0|
SeS1eS1eS36R3R2R1A3S35R3R2A2F_;Fn;Fp;Fhi;").
Proof. intros [|] p n H; [right | left]; exact H. Qed.
Lemma blk_cls_cases : ltac2:(tb__ "0|0|
S1eS1eS35R2R1A2S2aSeSeS36R1R4R3A3Lhi;A2F_;Fn;Fp;").
Proof. intros p n [H|H]; [exists false | exists true]; exact H. Qed.

Definition blk_geo (p n8 : Z) : Prop := ltac2:(tb__ "0|0|
S29S28S19S18S2cZ1000A2Vp;A2S19S18Vp;Vn8;A2S2bA2A2S19S18S2dZ10A2Vp;A2A2").
Definition cls_geo (hi : bool) (p n8 : Z) : Prop := ltac2:(tb__ "0|0|
SeOLhi;Vhi;S19S18S2dZ10A2Vp;A2S28S19S18S2cZ1000A2Vp;A2S19S18Vp;Vn8;A2S2bA2A2Xex2").
Lemma cls_geo_blk : ltac2:(tb__ "0|0|
SeS1eS1eS39R3R2R1A3S38R3R2A2F_;Fn8;Fp;Fhi;").
Proof. intros [|] p n8 H; [right | left]; exact H. Qed.

Lemma lo_round8 : ltac2:(tb__ "0|2|
S1eS1eS1eS27S1eS1aR3Z8M0A2Z0M1A3S27S1eS1aR2G0A2G1A3S1dR3S18R4G0A2A2S19S18R6R5A2S2bA2S19S18R7R5A2S2bA2F_;F_;F_;F_;Fn8;Fn;Fp;").
Proof.
  intros p n n8 Hp Hn8 Hlt Hle. unfold LOW_SHADOW_BEG in *.
  pose proof (Z.div_mod p 8 ltac:(lia)) as E1. pose proof (Z.div_mod n8 8 ltac:(lia)) as E2. rewrite Hp in E1. rewrite Hn8 in E2. lia.
Qed.

Definition F_pL : list sprop := ltac2:(tb__ "0|a|
SdS0S2S1S18Z7fff7f800000Z1000M0A2A1S5PaA1A2SdS0S7PcM1Z4A2SdS0S2S1S18S2cG0A2A1S5G1A1M2A2SdS0S2S6S30G2S1fA3M3S1S2bA1A2SdS0S4S6S30G2S5PdA1M4A3S1Z7fffff800000A1M5A2SdS0S2S1Z1A1G4A2SdS0SbS9S32G2S1Z0A1A3A1SdS0S4G2S1S1bZ2M6Z2fA2A1M7A2SdS0S7P69Z3M8A2SdS0S2G4S1fA2SdS0S4S1fS6S30G4S1Z8A1M9A3A2SdS0S2G3G5A2SdS0S2G9S1fA2SdS0S4S1fG7A2SdS0SaS6S31S21S1G8A1A3S1fA2SdS0S4S21S1S1bG6Z2cA2A1A2S12S0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition F_pc (hi : bool) : list sprop := if hi then F_p else F_pL.
Definition FACTSc (hi : bool) (W : list ulink) (st : ustop) (q : qvar) : list sprop := ltac2:(tb__ "0|0|
SfS0SfS0SfS0SfS0SfS0S42VW;Vst;A2S41S3fA1A3S47A3S34Vhi;A1A3S23A3S26Vq;A1A3").
Definition P0_fc (hi : bool) (W : list ulink) (st : ustop) (q : qvar) : axst := ltac2:(tb__ "0|1|
S40ScS3eS3cA1S45S44SdS14S11S3A2M0S13S11S3U4S1S49A1A4SdG0S13S11S3UbS5S3dA1A4S12G0A1A3A3A2S43S8S16S3A1S24VW;Vq;A2S33Vhi;VW;Vst;Vq;A4S48S17A9S12S14S3S3A2A1A2").
Lemma FACTSc_hi : ltac2:(tb__ "0|0|
S10S3aA1S3bS20S27S10S0A1S33S15R3R2R1A4S22R3R2R1A3A3Fq;Fst;FW;").
Proof. reflexivity. Qed.
Lemma P0_fc_hi : ltac2:(tb__ "0|0|
S10S3aA1S3bS20S27S46S37S15R3R2R1A4S25R3R2R1A3A3Fq;Fst;FW;").
Proof. reflexivity. Qed.

Lemma F_pc_hd : ltac2:(tb__ "0|0|
SeS27S0S4aS0S7P1Z0A2S34R1A1A3S2S1S18Z7fff7f800000Z1000A2A1S5PaA1A2A3Fhi;").
Proof. intros [|]; reflexivity. Qed.
End F0A_cls.

(* [comment removed for export] *)
Module F0A_c0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "sprop_below"; "swf"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "F_typ"; "PostQ1"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A"; "C4_0A"; "EQ_0A"; "q_0A"; "C2_0A_1"; "C2_0A_2"; "C3_0A"; "CD_0A"; "ED_0A_1"; "ED_0A_2"; "P0_0A"; "Ems_0A"; "Eps_0A"; "S1c_0A_1"; "S1c_0A_2"; "TM_0A"; "TQ_0A"; "run3_0A"; "run6_0A"; "RM_0A"; "RQ_0A"; "TM0_0A"; "TQ0_0A"; "run2_0A_1"; "run2_0A_2"; "run4_0A"; "run5_0A"; "EfD_0A_1"; "EfD_0A_2"; "Eq_0A"; "RD_0A_1"; "RD_0A_2"; "TDr_0A_1"; "TDr_0A_2"; "exits1_0A"; "run1_0A"; "Ebg_0A"; "Edr_0A"; "TD_0A_1"; "TD_0A_2"; "Xf_0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "sprop_below"; "swf"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "F_typ"; "PostQ1"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Be"; "C4_0Be"; "EQ_0Be"; "q_0Be"; "C2_0Be_1"; "C2_0Be_2"; "C3_0Be"; "CD_0Be"; "ED_0Be_1"; "ED_0Be_2"; "P0_0Be"; "Ems_0Be"; "Eps_0Be"; "S1c_0Be_1"; "S1c_0Be_2"; "TM_0Be"; "TQ_0Be"; "run3_0Be"; "run6_0Be"; "RM_0Be"; "RQ_0Be"; "TM0_0Be"; "TQ0_0Be"; "run2_0Be_1"; "run2_0Be_2"; "run4_0Be"; "run5_0Be"; "EfD_0Be_1"; "EfD_0Be_2"; "Eq_0Be"; "RD_0Be_1"; "RD_0Be_2"; "TDr_0Be_1"; "TDr_0Be_2"; "exits1_0Be"; "run1_0Be"; "Ebg_0Be"; "Edr_0Be"; "TD_0Be_1"; "TD_0Be_2"; "W_0Be"; "Xf_0Be"; "st_0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "sprop_below"; "swf"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "MSE"; "PSE"; "PreQ1"; "RETF"; "sM_of"; "sQ_of"; "F_typ"; "PostQ1"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Bf"; "C4_0Bf"; "EQ_0Bf"; "q_0Bf"; "C2_0Bf_1"; "C2_0Bf_2"; "C3_0Bf"; "CD_0Bf"; "ED_0Bf_1"; "ED_0Bf_2"; "P0_0Bf"; "Ems_0Bf"; "Eps_0Bf"; "S1c_0Bf_1"; "S1c_0Bf_2"; "TM_0Bf"; "TQ_0Bf"; "run3_0Bf"; "run6_0Bf"; "RM_0Bf"; "RQ_0Bf"; "TM0_0Bf"; "TQ0_0Bf"; "run2_0Bf_1"; "run2_0Bf_2"; "run4_0Bf"; "run5_0Bf"; "EfD_0Bf_1"; "EfD_0Bf_2"; "Eq_0Bf"; "RD_0Bf_1"; "RD_0Bf_2"; "TDr_0Bf_1"; "TDr_0Bf_2"; "exits1_0Bf"; "run1_0Bf"; "Ebg_0Bf"; "Edr_0Bf"; "TD_0Bf_1"; "TD_0Bf_2"; "W_0Bf"; "Xf_0Bf"; "st_0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
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

(* [comment removed for export] *)
Module F0A_c1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "F_typ"; "MSE"; "PSE"; "PreQ1"; "RETF"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "sQ_of"; "vH3"; "PostQ1"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1A"; "C4_1A"; "EQ_1A"; "q_1A"; "C2_1A_1"; "C2_1A_2"; "C2_1A_3"; "C3_1A"; "CD_1A"; "P0_1A"; "ED_1A_1"; "ED_1A_2"; "ED_1A_3"; "Ems_1A"; "Eps_1A"; "S1c_1A_1"; "S1c_1A_2"; "S1c_1A_3"; "TM_1A"; "TQ_1A"; "run3_1A"; "run6_1A"; "RM_1A"; "RQ_1A"; "TM0_1A"; "TQ0_1A"; "run1_1A"; "run2_1A_1"; "run2_1A_2"; "run2_1A_3"; "run4_1A"; "run5_1A"; "EfD_1A_1"; "EfD_1A_2"; "EfD_1A_3"; "Eq_1A"; "RD_1A_1"; "RD_1A_2"; "RD_1A_3"; "TDr_1A_1"; "TDr_1A_2"; "TDr_1A_3"; "exits1_1A"; "Ebg_1A"; "Edr_1A"; "TD_1A_1"; "TD_1A_2"; "TD_1A_3"; "Xf_1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_1A : list ulink := Wcan 1.
Definition st_1A : ustop := UStopLe.
Definition q_1A : qvar := QA.
Definition P0_1A : axst := P0_f W_1A st_1A q_1A.

Definition run1_1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S21SbS2A1A3S3fA3").

Definition S1c_1A_1 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z1A3").
Definition C2_1A_1 : axst := C2_of S1c_1A_1.
Definition run2_1A_1 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3aA3").
Definition EfD_1A_1 : axst := leaf 0 run2_1A_1.
Definition ED_1A_1 : axst := ED_of EfD_1A_1.
Definition RD_1A_1 : list sobj := RD_of ED_1A_1 1.
Definition TD_1A_1 : axst := TD_of ED_1A_1 1.
Definition TDr_1A_1 : axst := TDr_of TD_1A_1.
Definition S1c_1A_2 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z2A3").
Definition C2_1A_2 : axst := C2_of S1c_1A_2.
Definition run2_1A_2 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_1A_2 : axst := leaf 0 run2_1A_2.
Definition ED_1A_2 : axst := ED_of EfD_1A_2.
Definition RD_1A_2 : list sobj := RD_of ED_1A_2 2.
Definition TD_1A_2 : axst := TD_of ED_1A_2 2.
Definition TDr_1A_2 : axst := TDr_of TD_1A_2.
Definition S1c_1A_3 : axst := ltac2:(tb__ "0|0|
S29S36U0S50A2S17S5S3fA1A1Z3A3").
Definition C2_1A_3 : axst := C2_of S1c_1A_3.
Definition run2_1A_3 : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_1A_3 : axst := leaf 0 run2_1A_3.
Definition ED_1A_3 : axst := ED_of EfD_1A_3.
Definition RD_1A_3 : list sobj := RD_of ED_1A_3 3.
Definition TD_1A_3 : axst := TD_of ED_1A_3 3.
Definition TDr_1A_3 : axst := TDr_of TD_1A_3.
Definition exits1_1A : list axst := ltac2:(tb__ "0|0|
SaS4S45SaS4S46SaS4S47SbS4A1A3A3A3").

Definition CD_1A : axst := CD_of TDr_1A_1.
Definition run3_1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3").
Definition Eps_1A : axst := leaf 0 run3_1A.
Definition Ebg_1A : axst := leaf 1 run3_1A.
Definition C3_1A : axst := C3_of Eps_1A.
Definition run4_1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S25SbS2A1A3S3dA3").
Definition Ems_1A : axst := leaf 0 run4_1A.
Definition C4_1A : axst := C4_of Ems_1A.
Definition RM_1A : list sobj := RM_of C4_1A.
Definition TM0_1A : axst := TM0_of C4_1A.
Definition TM_1A : axst := TM_of C4_1A.
Definition run5_1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S23SbS2A1A3S48A3").
Definition Eq_1A : axst := leaf 0 run5_1A.
Definition EQ_1A : axst := EQ_of Eq_1A.
Definition RQ_1A : list sobj := RQ_of EQ_1A q_1A.
Definition TQ0_1A : axst := TQ0_of EQ_1A q_1A.
Definition TQ_1A : axst := TQ_of EQ_1A q_1A.
Definition run6_1A : list leafA := ltac2:(tb__ "0|0|
S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3").
Definition Edr_1A : axst := leaf 0 run6_1A.
Definition Xf_1A : axst := leaf 1 run6_1A.

Ltac vmr := vm_compute; reflexivity.
Lemma Cert1_1A : ltac2:(tb__ "0|0|
S0S9S77S68S1cSaS2S21SbS2A1A3S67SaS4S3fSbS4A1A3S60A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_1A exits1_1A run1_1A); [unfold run1_1A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_1A : ltac2:(tb__ "0|2|
S0S9S78S68S1cSaS2S21SbS2A1A3S67SaS75S76S3fZ1S1bZ0M0A1M1A3SbS75A1A3S7aS4S75S4S76R1G0G1A3LE;S60A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_1A 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_1A) run1_1A); [unfold run1_1A, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_1A_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6dS5S45A1S5S3aA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1A_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3aA1M0A1ScA3S1S0S3S13G0A1S13S5S45A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1A_1 : ltac2:(tb__ "0|0|
S0S9S69S67S13S5S3aA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1A_1 : ltac2:(tb__ "0|0|
S0S4S7S45S5S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma RUN2_1A_1 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3aA3S51A3"). Proof. unfold run2_1A_1; reflexivity. Qed.
Lemma L2_1A_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS51SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S51A2S56A3A2"). Proof. Time (split; [vmr | unfold EfD_1A_1; reflexivity]). Qed.
Lemma AXD_1A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS56S2aA2SeS4S40A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1A_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S6eS40S6bZ1M1A1S1fS40G1A2A3SeG0S5aA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1A_1 : ltac2:(tb__ "0|1|
S0S9S6fS40S6bZ1M0A1S1fS40G0A2S5aSaS4S6cG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1A_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS63S2bA2SeS4S5dA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1A_1 : ltac2:(tb__ "0|0|
S0S9S79S5dS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_1A_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6dS5S46A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1A_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S46A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1A_2 : ltac2:(tb__ "0|0|
S0S9S69S67S13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1A_2 : ltac2:(tb__ "0|0|
S0S4S7S46S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_1A_2 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3bA3S52A3"). Proof. unfold run2_1A_2; reflexivity. Qed.
Lemma L2_1A_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS52SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S52A2S57A3A2"). Proof. Time (split; [vmr | unfold EfD_1A_2; reflexivity]). Qed.
Lemma AXD_1A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS57S2aA2SeS4S41A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1A_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S6eS41S6bZ2M1A1S1fS41G1A2A3SeG0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1A_2 : ltac2:(tb__ "0|1|
S0S9S6fS41S6bZ2M0A1S1fS41G0A2S5bSaS4S6cG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1A_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS64S2bA2SeS4S5eA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1A_2 : ltac2:(tb__ "0|0|
S0S9S79S5eS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_1A_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S6dS5S47A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1A_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1A_3 : ltac2:(tb__ "0|0|
S0S9S69S67S13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1A_3 : ltac2:(tb__ "0|0|
S0S4S7S47S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_1A_3 : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S1dSbS2A1A3S3cA3S53A3"). Proof. unfold run2_1A_3; reflexivity. Qed.
Lemma L2_1A_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS53SaS2S1dSbS2A1A3A2ScA3S0S4S36U0S53A2S58A3A2"). Proof. Time (split; [vmr | unfold EfD_1A_3; reflexivity]). Qed.
Lemma AXD_1A_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS58S2aA2SeS4S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1A_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S6eS42S6bZ3M1A1S1fS42G1A2A3SeG0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1A_3 : ltac2:(tb__ "0|1|
S0S9S6fS42S6bZ3M0A1S1fS42G0A2S5cSaS4S6cG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1A_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6aS65S2bA2SeS4S5fA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1A_3 : ltac2:(tb__ "0|0|
S0S9S79S5fS3eA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S26SaS2S20SbS2A1A3A3S3eA3S4aA3"). Proof. unfold run3_1A; reflexivity. Qed.
Lemma L3_1A : ltac2:(tb__ "0|0|
S1S0S9S1eS4aSaS2S26SaS2S20SbS2A1A3A3A2ScA3S1S0S4S36U0S4aA2S44A3S0S4S36U1S4aA2S61A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_1A | unfold Ebg_1A]; reflexivity]). Qed.
Lemma NX3_1A : ltac2:(tb__ "0|1|
S1S0S9S69S67S13S5S3eA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_1A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6dS5S44A1S5S3dA1A2SeG2S12G0G1S33SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_1A : ltac2:(tb__ "0|0|
S0S4S7S44S5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma NX3b_1A : ltac2:(tb__ "0|0|
S0S9S69S67S13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_1A : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma RUN4_1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S25SbS2A1A3S3dA3S54A3"). Proof. unfold run4_1A; reflexivity. Qed.
Lemma L4_1A : ltac2:(tb__ "0|0|
S1S0S9S1eS54SaS2S25SbS2A1A3A2ScA3S0S4S36U0S54A2S43A3A2"). Proof. Time (split; [vmr | unfold Ems_1A; reflexivity]). Qed.
Lemma D4_1A : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S6dS5S43A1S5S37A1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_1A : ltac2:(tb__ "0|0|
S0S4S7S43S5S37A1A2S37A3"). Proof. vmr. Qed.
Lemma W4_1A : ltac2:(tb__ "0|1|
S1S0S9S19S5S37A1M0A1ScA3S1S0S3S13G0A1S13S5S43A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma HeM_1A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S6eS37S73S2dS37A1A3SeG0S4cA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_1A : ltac2:(tb__ "0|0|
S0S9S70S37S73S2dS37A1S4cS7aS6S4S8S74A4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_1A : ltac2:(tb__ "0|0|
S0S4S71S2dS37A1S73S31S37S4cA5S4eA3"). Proof. unfold TM0_1A, TM0_of, RM_1A; reflexivity. Qed.
Lemma FBM_1A : ltac2:(tb__ "0|3|
S1S0S9S72S15S1aS13S5S37A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S72S15S1aS13S5S4eA1A1A1G2A3ScA3S0S9S69S67G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETM_1A : ltac2:(tb__ "0|0|
S0S4S7bS4eS17S5S37A1A1A2S48A3"). Proof. vmr. Qed.
Lemma NX5_1A : ltac2:(tb__ "0|1|
S1S0S9S69S67S13S5S48A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S23SbS2A1A3S48A3S55A3"). Proof. unfold run5_1A; reflexivity. Qed.
Lemma L5_1A : ltac2:(tb__ "0|0|
S1S0S9S1eS55SaS2S23SbS2A1A3A2ScA3S0S4S36U0S55A2S59A3A2"). Proof. Time (split; [vmr | unfold Eq_1A; reflexivity]). Qed.
Lemma AXQ_1A : ltac2:(tb__ "0|0|
S0SfS4A1S6aS59S32A2SeS4S38A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_1A : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S6eS38S27S39A1S2eS38S39A2A3SeG0S4dA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_1A : ltac2:(tb__ "0|0|
S0S9S70S38S27S39A1S2eS38S39A2S4dSaS4S30S39A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_1A : ltac2:(tb__ "0|0|
S0S4S71S2eS38S39A2S27S39A1S30S39A1S38S4dA5S4fA3"). Proof. unfold TQ0_1A, TQ0_of, RQ_1A; reflexivity. Qed.
Lemma FBQ_1A : ltac2:(tb__ "0|3|
S1S0S9S72S15S1aS13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S72S15S1aS13S5S4fA1A1A1G2A3ScA3S0S9S69S67G1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETQ_1A : ltac2:(tb__ "0|0|
S0S4S7bS4fS17S5S38A1A1A2S49A3"). Proof. vmr. Qed.
Lemma NX6_1A : ltac2:(tb__ "0|1|
S1S0S9S69S67S13S5S49A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_1A : ltac2:(tb__ "0|0|
S0SdS6A1S35S1cSaS2S22SaS2S28SbS2A1A3A3S49A3S4bA3"). Proof. unfold run6_1A; reflexivity. Qed.
Lemma L6_1A : ltac2:(tb__ "0|0|
S1S0S9S1eS4bSaS2S22SaS2S28SbS2A1A3A3A2ScA3S1S0S4S36U0S4bA2S62A3S0S4S36U1S4bA2S66A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_1A | unfold Xf_1A]; reflexivity]). Qed.

End F0A_c1A.

(* [comment removed for export] *)
Module F0A_c1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "prod"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "sprop"; "ss_lenient"; "ss_facts"; "sobj"; "swf"; "sprop_below"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "DEPE"; "leaves_at"; "sD_of"; "BIGX"; "CASX"; "DRNE"; "ENQE"; "F_typ"; "MSE"; "PSE"; "PreQ1"; "RETF"; "S1c_of"; "XD"; "XDr"; "casx"; "sM_of"; "sQ_of"; "vH3"; "PostQ1"; "P0_f"; "PostMS"; "XQ"; "d3F"; "d4F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be"; "C4_1Be"; "EQ_1Be"; "q_1Be"; "C2_1Be_1"; "C2_1Be_2"; "C2_1Be_3"; "C3_1Be"; "CD_1Be"; "P0_1Be"; "ED_1Be_1"; "ED_1Be_2"; "ED_1Be_3"; "Ems_1Be"; "Eps_1Be"; "S1c_1Be_1"; "S1c_1Be_2"; "S1c_1Be_3"; "TM_1Be"; "TQ_1Be"; "run3_1Be"; "run6_1Be"; "RM_1Be"; "RQ_1Be"; "TM0_1Be"; "TQ0_1Be"; "run1_1Be"; "run2_1Be_1"; "run2_1Be_2"; "run2_1Be_3"; "run4_1Be"; "run5_1Be"; "EfD_1Be_1"; "EfD_1Be_2"; "EfD_1Be_3"; "Eq_1Be"; "RD_1Be_1"; "RD_1Be_2"; "RD_1Be_3"; "TDr_1Be_1"; "TDr_1Be_2"; "TDr_1Be_3"; "exits1_1Be"; "Ebg_1Be"; "Edr_1Be"; "TD_1Be_1"; "TD_1Be_2"; "TD_1Be_3"; "W_1Be"; "Xf_1Be"; "st_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_1Be : list ulink := Wcan 1.
Definition st_1Be : ustop := UStopLe.
Definition q_1Be : qvar := QBe.
Definition P0_1Be : axst := ltac2:(tb__ "0|0|
S31S67S69S3aA3").

Definition run1_1Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S21SbS2A1A3S40A3").

Definition S1c_1Be_1 : axst := ltac2:(tb__ "0|0|
S29S37U0S51A2S17S5S40A1A1Z1A3").
Definition C2_1Be_1 : axst := C2_of S1c_1Be_1.
Definition run2_1Be_1 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3bA3").
Definition EfD_1Be_1 : axst := leaf 0 run2_1Be_1.
Definition ED_1Be_1 : axst := ED_of EfD_1Be_1.
Definition RD_1Be_1 : list sobj := RD_of ED_1Be_1 1.
Definition TD_1Be_1 : axst := TD_of ED_1Be_1 1.
Definition TDr_1Be_1 : axst := TDr_of TD_1Be_1.
Definition S1c_1Be_2 : axst := ltac2:(tb__ "0|0|
S29S37U0S51A2S17S5S40A1A1Z2A3").
Definition C2_1Be_2 : axst := C2_of S1c_1Be_2.
Definition run2_1Be_2 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3cA3").
Definition EfD_1Be_2 : axst := leaf 0 run2_1Be_2.
Definition ED_1Be_2 : axst := ED_of EfD_1Be_2.
Definition RD_1Be_2 : list sobj := RD_of ED_1Be_2 2.
Definition TD_1Be_2 : axst := TD_of ED_1Be_2 2.
Definition TDr_1Be_2 : axst := TDr_of TD_1Be_2.
Definition S1c_1Be_3 : axst := ltac2:(tb__ "0|0|
S29S37U0S51A2S17S5S40A1A1Z3A3").
Definition C2_1Be_3 : axst := C2_of S1c_1Be_3.
Definition run2_1Be_3 : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S1dSbS2A1A3S3dA3").
Definition EfD_1Be_3 : axst := leaf 0 run2_1Be_3.
Definition ED_1Be_3 : axst := ED_of EfD_1Be_3.
Definition RD_1Be_3 : list sobj := RD_of ED_1Be_3 3.
Definition TD_1Be_3 : axst := TD_of ED_1Be_3 3.
Definition TDr_1Be_3 : axst := TDr_of TD_1Be_3.
Definition exits1_1Be : list axst := ltac2:(tb__ "0|0|
SaS4S46SaS4S47SaS4S48SbS4A1A3A3A3").

Definition CD_1Be : axst := CD_of TDr_1Be_1.
Definition run3_1Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S26SaS2S20SbS2A1A3A3S3fA3").
Definition Eps_1Be : axst := leaf 0 run3_1Be.
Definition Ebg_1Be : axst := leaf 1 run3_1Be.
Definition C3_1Be : axst := C3_of Eps_1Be.
Definition run4_1Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S25SbS2A1A3S3eA3").
Definition Ems_1Be : axst := leaf 0 run4_1Be.
Definition C4_1Be : axst := C4_of Ems_1Be.
Definition RM_1Be : list sobj := RM_of C4_1Be.
Definition TM0_1Be : axst := TM0_of C4_1Be.
Definition TM_1Be : axst := TM_of C4_1Be.
Definition run5_1Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S23SbS2A1A3S49A3").
Definition Eq_1Be : axst := leaf 0 run5_1Be.
Definition EQ_1Be : axst := EQ_of Eq_1Be.
Definition RQ_1Be : list sobj := RQ_of EQ_1Be q_1Be.
Definition TQ0_1Be : axst := TQ0_of EQ_1Be q_1Be.
Definition TQ_1Be : axst := TQ_of EQ_1Be q_1Be.
Definition run6_1Be : list leafA := ltac2:(tb__ "0|0|
S36S1cSaS2S22SaS2S28SbS2A1A3A3S4aA3").
Definition Edr_1Be : axst := leaf 0 run6_1Be.
Definition Xf_1Be : axst := leaf 1 run6_1Be.

Ltac vmr := vm_compute; reflexivity.
Lemma Cert1_1Be : ltac2:(tb__ "0|0|
S0S9S7aS6bS1cSaS2S21SbS2A1A3S6aSaS4S40SbS4A1A3S61A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_1Be exits1_1Be run1_1Be); [unfold run1_1Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_1Be : ltac2:(tb__ "0|2|
S0S9S7bS6bS1cSaS2S21SbS2A1A3S6aSaS78S79S40Z1S1bZ0M0A1M1A3SbS78A1A3S7dS4S78S4S79R1G0G1A3LE;S61A4A6ScA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_1Be 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_1Be) run1_1Be); [unfold run1_1Be, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_1Be_1 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S70S5S46A1S5S3bA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1Be_1 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3bA1M0A1ScA3S1S0S3S13G0A1S13S5S46A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1Be_1 : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3bA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1Be_1 : ltac2:(tb__ "0|0|
S0S4S7S46S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_1Be_1 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3bA3S52A3"). Proof. unfold run2_1Be_1; reflexivity. Qed.
Lemma L2_1Be_1 : ltac2:(tb__ "0|0|
S1S0S9S1eS52SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S52A2S57A3A2"). Proof. Time (split; [vmr | unfold EfD_1Be_1; reflexivity]). Qed.
Lemma AXD_1Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS57S2aA2SeS4S41A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1Be_1 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S71S41S6eZ1M1A1S1fS41G1A2A3SeG0S5bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1Be_1 : ltac2:(tb__ "0|1|
S0S9S72S41S6eZ1M0A1S1fS41G0A2S5bSaS4S6fG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1Be_1 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS64S2bA2SeS4S5eA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1Be_1 : ltac2:(tb__ "0|0|
S0S9S7cS5eS3fA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_1Be_2 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S70S5S47A1S5S3cA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1Be_2 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3cA1M0A1ScA3S1S0S3S13G0A1S13S5S47A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1Be_2 : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3cA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1Be_2 : ltac2:(tb__ "0|0|
S0S4S7S47S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_1Be_2 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3cA3S53A3"). Proof. unfold run2_1Be_2; reflexivity. Qed.
Lemma L2_1Be_2 : ltac2:(tb__ "0|0|
S1S0S9S1eS53SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S53A2S58A3A2"). Proof. Time (split; [vmr | unfold EfD_1Be_2; reflexivity]). Qed.
Lemma AXD_1Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS58S2aA2SeS4S42A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1Be_2 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S71S42S6eZ2M1A1S1fS42G1A2A3SeG0S5cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1Be_2 : ltac2:(tb__ "0|1|
S0S9S72S42S6eZ2M0A1S1fS42G0A2S5cSaS4S6fG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1Be_2 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS65S2bA2SeS4S5fA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1Be_2 : ltac2:(tb__ "0|0|
S0S9S7cS5fS3fA2ScA3"). Proof. Time vmr. Qed.
Lemma D2_1Be_3 : ltac2:(tb__ "0|4|
S0SfS10SdS10S14S14A2M0A1M1SdS15A1M2A2M3A1S70S5S48A1S5S3dA1A2SeG3S12G1G2SaG0S12S14S14S2cS2fA4SbG0A1A3S24A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_1Be_3 : ltac2:(tb__ "0|1|
S1S0S9S19S5S3dA1M0A1ScA3S1S0S3S13G0A1S13S5S48A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma NX2_1Be_3 : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3dA1A1A2ScA3"). Proof. vmr. Qed.
Lemma EQ2_1Be_3 : ltac2:(tb__ "0|0|
S0S4S7S48S5S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma RUN2_1Be_3 : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S1dSbS2A1A3S3dA3S54A3"). Proof. unfold run2_1Be_3; reflexivity. Qed.
Lemma L2_1Be_3 : ltac2:(tb__ "0|0|
S1S0S9S1eS54SaS2S1dSbS2A1A3A2ScA3S0S4S37U0S54A2S59A3A2"). Proof. Time (split; [vmr | unfold EfD_1Be_3; reflexivity]). Qed.
Lemma AXD_1Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS59S2aA2SeS4S43A2A3"). Proof. Time vmr. Qed.
Lemma HeD_1Be_3 : ltac2:(tb__ "0|2|
S0SfSdS18A1M0A1S71S43S6eZ3M1A1S1fS43G1A2A3SeG0S5dA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_1Be_3 : ltac2:(tb__ "0|1|
S0S9S72S43S6eZ3M0A1S1fS43G0A2S5dSaS4S6fG0A1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma AXDr_1Be_3 : ltac2:(tb__ "0|0|
S0SfS4A1S6dS66S2bA2SeS4S60A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_1Be_3 : ltac2:(tb__ "0|0|
S0S9S7cS60S3fA2ScA3"). Proof. Time vmr. Qed.
Lemma RUN3_1Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S26SaS2S20SbS2A1A3A3S3fA3S4bA3"). Proof. unfold run3_1Be; reflexivity. Qed.
Lemma L3_1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS4bSaS2S26SaS2S20SbS2A1A3A3A2ScA3S1S0S4S37U0S4bA2S45A3S0S4S37U1S4bA2S62A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_1Be | unfold Ebg_1Be]; reflexivity]). Qed.
Lemma NX3_1Be : ltac2:(tb__ "0|1|
S1S0S9S6cS6aS13S5S3fA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma D3_1Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S70S5S45A1S5S3eA1A2SeG2S12G0G1S34SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_1Be : ltac2:(tb__ "0|0|
S0S4S7S45S5S3eA1A2S3eA3"). Proof. vmr. Qed.
Lemma NX3b_1Be : ltac2:(tb__ "0|0|
S0S9S6cS6aS13S5S3eA1A1A2ScA3"). Proof. vmr. Qed.
Lemma W3_1Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S3eA1M0A1ScA3S1S0S3S13G0A1S13S5S45A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma RUN4_1Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S25SbS2A1A3S3eA3S55A3"). Proof. unfold run4_1Be; reflexivity. Qed.
Lemma L4_1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS55SaS2S25SbS2A1A3A2ScA3S0S4S37U0S55A2S44A3A2"). Proof. Time (split; [vmr | unfold Ems_1Be; reflexivity]). Qed.
Lemma D4_1Be : ltac2:(tb__ "0|3|
S0SfS10SdS10S14S14A2A1M0SdS15A1M1A2M2A1S70S5S44A1S5S38A1A2SeG2S12G0G1S35SbS15A1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_1Be : ltac2:(tb__ "0|0|
S0S4S7S44S5S38A1A2S38A3"). Proof. vmr. Qed.
Lemma W4_1Be : ltac2:(tb__ "0|1|
S1S0S9S19S5S38A1M0A1ScA3S1S0S3S13G0A1S13S5S44A1A1A3S0S9S16G0A1S11A3A2A2"). Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma HeM_1Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S71S38S76S2dS38A1A3SeG0S4dA2A3"). Proof. Time vmr. Qed.
Lemma HchkM_1Be : ltac2:(tb__ "0|0|
S0S9S73S38S76S2dS38A1S4dS7dS6S4S8S77A4A5ScA3"). Proof. Time vmr. Qed.
Lemma HTM_1Be : ltac2:(tb__ "0|0|
S0S4S74S2dS38A1S76S32S38S4dA5S4fA3"). Proof. unfold TM0_1Be, TM0_of, RM_1Be; reflexivity. Qed.
Lemma FBM_1Be : ltac2:(tb__ "0|3|
S1S0S9S75S15S1aS13S5S38A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S75S15S1aS13S5S4fA1A1A1G2A3ScA3S0S9S6cS6aG1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETM_1Be : ltac2:(tb__ "0|0|
S0S4S7eS4fS17S5S38A1A1A2S49A3"). Proof. vmr. Qed.
Lemma NX5_1Be : ltac2:(tb__ "0|1|
S1S0S9S6cS6aS13S5S49A1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN5_1Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S23SbS2A1A3S49A3S56A3"). Proof. unfold run5_1Be; reflexivity. Qed.
Lemma L5_1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS56SaS2S23SbS2A1A3A2ScA3S0S4S37U0S56A2S5aA3A2"). Proof. Time (split; [vmr | unfold Eq_1Be; reflexivity]). Qed.
Lemma AXQ_1Be : ltac2:(tb__ "0|0|
S0SfS4A1S6dS5aS33A2SeS4S39A2A3"). Proof. Time vmr. Qed.
Lemma HeQ_1Be : ltac2:(tb__ "0|1|
S0SfSdS18A1M0A1S71S39S27S3aA1S2eS39S3aA2A3SeG0S4eA2A3"). Proof. Time vmr. Qed.
Lemma HchkQ_1Be : ltac2:(tb__ "0|0|
S0S9S73S39S27S3aA1S2eS39S3aA2S4eSaS4S30S3aA1SbS4A1A3A5ScA3"). Proof. Time vmr. Qed.
Lemma HTQ_1Be : ltac2:(tb__ "0|0|
S0S4S74S2eS39S3aA2S27S3aA1S30S3aA1S39S4eA5S50A3"). Proof. unfold TQ0_1Be, TQ0_of, RQ_1Be; reflexivity. Qed.
Lemma FBQ_1Be : ltac2:(tb__ "0|3|
S1S0S9S75S15S1aS13S5S39A1M0A1M1A1S17G0A1M2A3ScA3S1S0S9S75S15S1aS13S5S50A1A1A1G2A3ScA3S0S9S6cS6aG1A2ScA3A2A2").
Proof. Time (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2). Qed.
Lemma ETQ_1Be : ltac2:(tb__ "0|0|
S0S4S7eS50S17S5S39A1A1A2S4aA3"). Proof. vmr. Qed.
Lemma NX6_1Be : ltac2:(tb__ "0|1|
S1S0S9S6cS6aS13S5S4aA1M0A1A2ScA3S0S9S16G0A1S11A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RUN6_1Be : ltac2:(tb__ "0|0|
S0SdS6A1S36S1cSaS2S22SaS2S28SbS2A1A3A3S4aA3S4cA3"). Proof. unfold run6_1Be; reflexivity. Qed.
Lemma L6_1Be : ltac2:(tb__ "0|0|
S1S0S9S1eS4cSaS2S22SaS2S28SbS2A1A3A3A2ScA3S1S0S4S37U0S4cA2S63A3S0S4S37U1S4cA2S68A3A2A2"). Proof. Time (split; [vmr | split; [unfold Edr_1Be | unfold Xf_1Be]; reflexivity]). Qed.

End F0A_c1Be.

