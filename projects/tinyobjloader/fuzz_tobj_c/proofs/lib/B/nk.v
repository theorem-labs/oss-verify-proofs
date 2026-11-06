(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.

(* [comment removed for export] *)
Module Lib_fuzz_iface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SPUle"; "sobj"; "SVar"; "DUnknown"; "SAlu"; "cell"; "mkObj"; "valuation"; "FcsrFrm0"; "SPAlign"; "SPBranch"; "mkSS"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nil"; "list"; "app"; "nat"; "None"; "false"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "A_globals"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "vDAT"; "vLEN"; "vDp"; "P0_fz"; "spm"; "vTOPfz"; "O_F_fz"; "O_W_fz"; "O_pay"; "Pre_fz"; "X_fz"; "fz_facts"; "nd_fz0"; "PD_fz"; "P_fz"; "X_lits"; "bd_fz"; "nd_fz1"; "two40"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "ANone"; "JA_pre"; "NDA"; "JLA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "BI"; "BXok_d"; "KU"; "bxt"; "uval"; "ASv"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "add"; "div"; "le"; "lt"; "mul"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.FZAddr"; "D_FZ"; "fz_frame"; "FZ_DEPTH"; "fz_entry"; "fz_ret"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.Stmt"; "Posts_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "aceil"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "CK0"; "CK_DIV"; "CV"; "CV0"; "MAX_INPUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module FZAddr.
  Definition fz_entry : Z := 0x9bbec.
  Definition fz_ret : Z := 0x9bf70.
  Definition fz_frame : Z := 288.

  Definition FZ_DEPTH : Z := 32768.

  Definition D_FZ : Z := 33056.
End FZAddr.
Import FZAddr.

Definition two47 : Z := 2 ^ 47. Definition two40 : Z := 2 ^ 40.
Definition spm (k : Z) : sv := ltac2:(tb__ "0|0|
S7S4dS5PaA1S1S46Vk;A1A1A3").
Definition vDAT : sv := SVar 12. Definition vLEN : sv := SVar 13. Definition vDp : sv := SVar 19.

Definition O_F_fz : sobj := ltac2:(tb__ "0|0|
S9S5PaA1S1S46S50A1A1S1Z0A1S12S8A1S6A5").
Definition O_W_fz : sobj := ltac2:(tb__ "0|0|
S9S23S50A1S21S1Z0A1S12S8A1S6A5").
Definition O_pay : sobj := ltac2:(tb__ "0|0|
S9S1fS1Z0A1S20S12S8A1S6A5").

Definition vTOPfz : sv := SVar 30.
Definition fz_facts : list sprop := ltac2:(tb__ "0|7|
SfS2ScPaM0Z4M1A2SfS2S3S5G0A1M2S1S4cS32Ze0A2A1A2SfS2S3S1S5cA1M3S7S4dS23S50A1M4S21A3M5A2SfS2S3G3G4A2SfS2S3G3G2A2SfS2S3S24G5A2SfS2S3G3S24A2SfS2S3S24S1Z7fffff800000A1M6A2SfS2SdS4eS1S46S51A1A1S21A3SfS2SdS4eS21S1S46S31A1A1A3SfS2ScPcG1A2SfS2S3S1Z1000A1S1fA2SfS2S3S7S4dS1fS20A3G6A2SfS2S3S1fG6A2SfS2S3S20S1S66A1A2SfS2S3S5P1cA1G2A2SfS2S3S1S47S5cS4fA2A1G2A2S12S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_lits : list (sv * sv) := ltac2:(tb__ "0|5|
SfS11S0S0A2M0S10S0S0S1Z22ba0A1S1ZcA1M1A4SfG0S10S0S0S1Z22bc0A1S1Z2A1M2A4SfG0S10S0S0S1Z22be0A1S1Z3A1M3A4SfG0S10S0S0S1Z22c00A1G3A4SfG0S10S0S0S1Z22c20A1G2A4SfG0S10S0S0S1Z22c40A1G2A4SfG0S10S0S0S1Z22c60A1G2A4SfG0S10S0S0S1Z22c80A1G2A4SfG0S10S0S0S1Z22ca0A1G2A4SfG0S10S0S0S1Z22cc0A1S1Z7A1M4A4SfG0S10S0S0S1Z22ce0A1G4A4SfG0S10S0S0S1Z22d00A1G3A4SfG0S10S0S0S1Z22d20A1G2A4SfG0S10S0S0S1Z22d40A1S1Z4A1A4SfG0S10S0S0S1Z22d60A1S1Z2eA1A4SfG0S10S0S0S1Z22dc0A1S1Z2cA1A4SfG0S10S0S0S1Z22e20A1G1A4SfG0S10S0S0S1Z239c0A1S1Zb8A1A4S12G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Fixpoint in_litsL (l : list (sv * sv)) (a : Z) : Prop :=
  match l with
  | [] => False
  | (SLit b, SLit n) :: r => (b <= a < b + n) \/ in_litsL r a
  | _ :: r => in_litsL r a
  end.
Definition in_lits (a : Z) : Prop := in_litsL X_lits a.

Definition X_fz : list (sv * sv) := ltac2:(tb__ "0|1|
S14S11S0S0A2M0SfG0S10S0S0S1fS20A4SfG0S10S0S0S23S4fA1S1S4fA1A4S12G0A1A3A3S2eA3").
Definition Pre_fz : axst := ltac2:(tb__ "0|0|
S1eSeS52S3cS3aSbS16S0A1S14S4SfS4S25SfS4S26SfS4S27S12S4A1A3A3A3S1dA3S2aS39S17A9S29A2").
Definition P_fz : axst := ltac2:(tb__ "0|1|
S1eSeS53S3dS3bS39A1SfS11S15S0A2M0S10S15S0UaS1Z0A1A4S12G0A1A3A2S3aSbS16S0A1S14S4SfS4S25SfS4S26SfS4S27S12S4A1A3A3A3S1dA3S2aS67S17A9S29A2").

Definition bd_fz : list bitem := ltac2:(tb__ "0|5|
SfS3eS40Z1M0Z0M1SfS11S1aS3fA2M2S10S1aS3fS64S45S20A1M3A4S12G2A1M4A3S65A4SfS3eS40G1G0SfG2S10S1aS3fS48S42S63A2G3A4G4A3S4bS42S62A2A4S12S3eA1A3A3").
Definition nd_fz0 : ndesc := ltac2:(tb__ "0|0|
S37S12S11S0S0A2A1S12S11S11S0S1aA2S0A2A1S2fS35A4").
Definition nd_fz1 : ndesc := ltac2:(tb__ "0|0|
S37S12S11S0S0A2A1S12S11S11S0S1aA2S0A2A1S12S3eA1S35A4").

Definition PD_fz : list (axst * ndesc) := ltac2:(tb__ "0|1|
SfS11S1bS33A2M0S10S1bS33S2dS30A4S12G0A1A3").

Definition P0_fz (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S55S1aS55S49S44Vr;S1fA2M0R1A2S4aR1S47G0S44Vr;S20A2A2A2A2S60VCST;Vr;VFB;VFF;R2A5F_;Fa;S1aS56S15S61R1S57S11S11S1aS1aA2M1S1aA2G1S18G1S1aA2VFF;A4A2U0A3Fc;A2").

Section Stmt.
Variable AInv : ltac2:(tb__ "0|0|
S68SaS13S54Q40A1A1S5dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable Kc : KcA.

Definition Posts_fz (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (BX : bxt) : list (axst * jpostA) := ltac2:(tb__ "0|1|
S57S11S1bS33A2M0S11S1bS5bA2G0S10S1bS5bS18S1bS33R1A3S38VAInv;VCST;VXGL;VKc;S22VCST;VFB;VFF;A3VFB;VFF;VBX;S34S19S1bS33R1A3AaA4Ld;S2cA4").

Definition fuzz_one_sumT (ok : world -> Prop) : Prop := ltac2:(tb__ "0|1|
S13S11S1aS1aA2M0A1S13S11G0S1aA2A1S43SaS13S54Q40A1A1S41Z8R3A2S5fS1cVok;S59S1cS36VAInv;VCST;VXGL;VKc;S22VCST;R6R5A3R6R5R4S34S2bAaS28R3R2A5S5aS1cS39R3R2S58R6R5R4A3A5A4F_;Ftp0;Frho0;FBX;FFF;FFB;").
Definition fuzz_one_sumE : Prop := ltac2:(tb__ "0|1|
S13S11S1aS1aA2M0A1S13S11G0S1aA2A1S43SaS13S54Q40A1A1S41Z8R3A2S5eS1cS59S1cS36VAInv;VCST;VXGL;VKc;S22VCST;R6R5A3R6R5R4S34S2bAaS28R3R2A5S5aS1cS39R3R2S58R6R5R4A3A5A3F_;Ftp0;Frho0;FBX;FFF;FFB;").
End Stmt.

Goal swf (ax_S Pre_fz) = true /\ axwf Pre_fz = true /\ swf (ax_S P_fz) = true /\ axwf P_fz = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_fuzz_iface.

(* [comment removed for export] *)
Module Lib_realloc_darr.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "list"; "prod"; "nat"; "app"; "false"; "None"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "SPUle"; "cell"; "SVar"; "SAlu"; "mkObj"; "SPBranch"; "FcsrFrm0"; "SPAlign"; "mkSS"; "DUnknown"; "ss_regs"; "mkCell"; "ob_base"; "ob_hi"; "ob_lo"; "ss_next"; "tfact"; "DArr"; "SMd"; "SPNot"; "TF2le"; "ob_dflt"; "rw"; "ss_facts"; "ss_fregs"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_realloc_darr"; "kb16"; "vK"; "VQ"; "vKn"; "vQ"; "vPn"; "ndR"; "vP"; "z0"; "c8"; "vA"; "vD"; "X_cp0"; "darr"; "eoff"; "pN"; "tv0"; "O_D"; "O_F"; "O_al"; "bd1"; "ra_facts"; "two47"; "vF0"; "vF1"; "B32"; "E_m"; "FUEL_ra"; "O_old"; "Pre_ra"; "X_step"; "bd0"; "cutpcs_ra"; "spm"; "tmpl"; "tv1"; "C_0"; "D_1"; "D_10"; "D_11"; "D_12"; "D_13"; "D_14"; "D_15"; "D_2"; "D_3"; "D_4"; "D_5"; "D_6"; "D_7"; "D_8"; "D_9"; "E_free"; "E_freeT"; "O_new"; "P_fail"; "P_ok"; "P_ok_S"; "Pre_f"; "Pre_m"; "T_free"; "T_mnull"; "T_mok"; "X_cp0f"; "X_f"; "cp_regs"; "cutsE"; "exitsE"; "flds"; "leafA_at"; "ok_facts"; "pre_regs_ra"; "q_facts"; "src_cells"; "tv2"; "tvP"; "two40"; "vL"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ejcertA"; "tv_factsA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "ALU_SUB"; "BC_GE"; "BC_EQ"; "M_MUL"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BIc"; "BIs"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@Corelib.Init.Logic"; "ex"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "leavesA_at"; "mkA"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_realloc_darr.ReallocAddr"; "ra_L"; "ra_ret"; "free_pc"; "malloc_pc"; "ra_entry"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "opp"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops"; "bl_prune"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "tmpl_inst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV CellTile ArrMat.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
Module ReallocAddr. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc.ReallocAddr. End ReallocAddr.
Import ReallocAddr.

Definition FUEL_ra : nat := 400%nat.
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.
Definition B32 : Z := 4294967295.

Definition vA : sv := SVar 12. Definition vP : sv := SVar 13. Definition vK : sv := SVar 14. Definition vKn : sv := SVar 33.
Definition vD : sv := SVar 19. Definition vUD : sv := SVar 52. Definition vL : sv := SVar 53.
Definition spm (k : Z) : sv := ltac2:(tb__ "0|0|
S12S80S11PaA1SeSa1Vk;A1A1A3").
Definition kb16 (k : sv) : sv := SMd M_MUL (SLit 16) k.
Definition flds : list (Z * Z) := ltac2:(tb__ "0|2|
S0S4S29S29A2M0S1S29S29Z0Z8M1A4S0G0S1S29S29G1G1A4S2G0A1A3A3").
Definition tmpl : list tfact := ltac2:(tb__ "0|0|
S0S1fS23S7U0U1S78A4S2S1fA1A3").
Definition darr (c : sv) : odefault := ltac2:(tb__ "0|0|
S20Z10Vc;S6fS4dA4").

Definition c8 (o : Z) (v : sv) : cell := mkCell (SLit o) 8 v.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S13S11PaA1SeN60A1SeZ0A1Vcells;S18A5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S13S4cZ60A1S36SeZ0A1S2S10A1S18A5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S13S35SeZ0M0A1M1SeZ30A1S0S10S34G0SeS9cA1A2S0S10S34Z8SeS9dA1A2S0S10S34Z10G1A2S0S10S34Z18SeS9eA1A2S0S10S34Z20G1A2S0S10S34Z28S79A2S2S10A1A3A3A3A3A3A3S18A5").
Definition O_old : sobj := ltac2:(tb__ "0|0|
S13S32SeZ0A1S2bS2cA1S2S10A1S38S2cA1A5").

Definition ra_facts : list sprop := ltac2:(tb__ "0|9|
S0SdS16PaM0Z4M1A2S0SdSfS11G0A1M2SeS41A1M3A2S0SdSfS11P1eA1M4S12S80S4cZ60A1M5S36A3A2S0SdSfG4G5A2S0SdSfG4G2A2S0SdS14S83SeN1000A1S36A3S0SdS14S83S36SeSa1S77A1A1A3S0SdS16PcZ3A2S0SdSfSeZ1000A1M6S35A2S0SdSfS12S80S35SeZ30A1A3G4A2S0SdSfS35G3A2S0SdS16PdG1A2S0SdSfG6S32A2S0SdSfS12S80S32S2bS2cA1A3G4A2S0SdSfS32G3A2S0SdSfSeZ1A1S2cA2S0SdS14S81S2cS2eA3S0SdSfS2bS2eA1SeS44A1M7A2S0SdSfS2eG7A2S0SdSfSeZ7fff7f800000A1M8G4A2S0SdSfG4SeZ7fffff800000A1A2S0SdSfG8G2A2S2SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition pre_regs_ra : list sv := ltac2:(tb__ "0|1|
S8dS8fS0S4S5SbA2M0S1S5SbUcS2bS2cA1A4S0G0S1S5SbUdS2bS2eA1A4S0G0S1S5SbUeSeZ10A1A4S2G0A1A3A3A3A2").
Definition X_ra : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SbSbA2M0S1SbSbS35SeZ30A1A4S0G0S1SbSbS32S2bS2cA1A4S2G0A1A3A3").
Definition Pre_ra_S : sstate := ltac2:(tb__ "0|0|
S17S9bS72S8cS15S8SbA1S6ScS0ScS3dS2S10A1A1S0ScS3cS0ScS3eS0ScS47S2ScA1A3A3A3A3S93A3S40S8bS7A9").
Definition Pre_ra : axst := mkA Pre_ra_S X_ra.

Definition cutpcs_ra : list Z := ltac2:(tb__ "0|0|
S0S29S97S0S29S9aS0S29S99S2S29A1A3A3A3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_ra end.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_ra_S end.
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S86S7aVk;S94S46S4bVS;Vpc;A4S48A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition E_m : axst := Eval vm_compute in leafA_at Pre_ra malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S4S2aSbA2S1S2aSbPfS36A4Sa3PaS7bS45A1S7bS66A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := pos_add_nat (ss_next (ax_S E_m)) 10.
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := ltac2:(tb__ "0|0|
S7fS1SbSbS11S3aA1S2bS2eA1A4A1").
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition X_cp0 : axst := Eval vm_compute in leafA_at T_mok ra_L 0.

Definition vQ : sv := SVar 172.  Definition vF0 : sv := SVar 173.  Definition vF1 : sv := SVar 174.
Definition eoff (j : Z) : sv := ltac2:(tb__ "0|0|
S12S80S2bS2fA1SeVj;A1A3").
Definition pls (b : sv) (o : sv) : sv := SAlu ALU_ADD b o.
Definition cp_regs : list sv := ltac2:(tb__ "0|12|
S3SbA1M0G0Lx;S19S7bS37A1A1S2SbA1M1SbG0G0G0Ll;R1S0SbR2G1A3M2SbG0G0G0Ll0;R1S0SbR4G2A3M3SbG0G0G0Ll1;R1S0SbR6G3A3M4SbG0G0G0Ll2;R1S0SbR8G4A3M5SbG0G0G0Ll3;R1S0SbRaG5A3M6SbG0G0G0Ll4;R1S0SbRcG6A3M7SbG0G0G0Ll5;R1S0SbReG7A3M8SbG0G0G0Ll6;R1S0SbR10G8A3M9SbG0G0G0Ll7;R1S0SbR12G9A3MaSbG0G0G0Ll8;R1S0SbR14GaA3MbSbG0G0G0Ll9;R1S0SbR16GbA3McSbG0G0G0Ll10;R1S0SbR18GcA3MdSbG0G0G0Ll11;R1S0SbR1aGdA3MeSbG0G0G0Ll12;R1S0SbR1cGeA3MfSbG0G0G0Ll13;R1S0SbR1eGfA3M10SbG0G0G0Ll14;R1S0SbR20G10A3M11SbG0G0G0Ll15;R1S0SbR22G11A3SbG0S0SbR24S0SbR22S0SbR20S0SbR1eS0SbR1cS0SbR1aS0SbR18S0SbS11Pb0A1S0SbR14S0SbR12S0SbR10S0SbReS0SbRcS0SbRaS0SbS11PafA1S0SbS11Pb1A1S0SbR4S0SbS2bS2fA1R1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Lrest;Lr17;X3x2Ll15;Lr16;X3x2Ll14;Lr15;X3x2Ll13;Lr14;X3x2Ll12;Lr13;X3x2Ll11;Lr12;X3x2Ll10;Lr11;X3x2Ll9;Lr10;X3x2Ll8;Lr9;X3x2Ll7;Lr8;X3x2Ll6;Lr7;X3x2Ll5;Lr6;X3x2Ll4;Lr5;X3x2Ll3;Lr4;X3x2Ll2;Lr3;X3x2Ll1;Lr2;X3x2Ll0;Lr1;X3x2Ll;Lr0;X3x2").
Definition src_cells : list cell := ltac2:(tb__ "0|1|
S0S10S1aS2bS2fA1Z8M0S42A3S0S10S1aS39G0A1G0S43A3S2S10A1A3A3").
Definition q_facts : list sprop := ltac2:(tb__ "0|1|
S6SdS0SdS14S81S2fS2cA3S0SdSfS39Z10A1M0S2bS2cA1A2S0SdSfG0S2bS2eA1A2S0SdSfS2fSeS44A1A2S2SdA1A3A3A3A3Sa6S0SbS42S0SbS43S2SbA1A3A3S4dA2A3").
Definition C_0c : axst := ltac2:(tb__ "0|9|
S7cS37S17S97S6cS27S7bS37A1M0A1S15S8SbA1S3ScA1M1G1Lx;S28G0A1S2ScA1M2ScG1G1G1Ll;R1S0ScR2G2A3M3ScG1G1G1Ll0;R1S0ScR4G3A3M4ScG1G1G1Ll1;R1S0ScR6G4A3M5ScG1G1G1Ll2;R1S0ScR8G5A3M6ScG1G1G1Ll3;R1S0ScRaG6A3M7ScG1G1G1Ll4;R1S0ScRcG7A3ScG1G1G1Ll5;R1S0ScReS0ScS13S11S3aA1SeZ0A1M8S2bS2eA1S2S10A1S38S2fA1A5S0ScRaS0ScR8S0ScR6S0ScR4S0ScS13S32G8S2bS2cA1S74S38S2cA1A5G2A3A3A3A3A3A3A3ScG1S0ScR10S0ScReS0ScRcS0ScRaS0ScR8S0ScR6S0ScR4S0ScR2R1A3A3A3A3A3A3A3A3Ll6;Ls;X3x2Ll5;Lo6;X3x2Ll4;Lo5;X3x2Ll3;Lo4;X3x2Ll2;Lo3;X3x2Ll1;Lo2;X3x2Ll0;Lo1;X3x2Ll;Lo0;X3x2S6SdS73S26G0A1A3Pb2S7A9A2").
Definition C_0 : axst := Eval vm_compute in C_0c.

Definition stepD (S : axst) : axst := ltac2:(tb__ "0|0|
Sa5Pb2S70VS;S97U0A3A2").
Definition D_1 : axst := Eval vm_compute in stepD C_0.
Definition D_2 : axst := Eval vm_compute in stepD D_1.
Definition D_3 : axst := Eval vm_compute in stepD D_2.
Definition D_4 : axst := Eval vm_compute in stepD D_3.
Definition D_5 : axst := Eval vm_compute in stepD D_4.
Definition D_6 : axst := Eval vm_compute in stepD D_5.
Definition D_7 : axst := Eval vm_compute in stepD D_6.
Definition D_8 : axst := Eval vm_compute in stepD D_7.
Definition D_9 : axst := Eval vm_compute in stepD D_8.
Definition D_10 : axst := Eval vm_compute in stepD D_9.
Definition D_11 : axst := Eval vm_compute in stepD D_10.
Definition D_12 : axst := Eval vm_compute in stepD D_11.
Definition D_13 : axst := Eval vm_compute in stepD D_12.
Definition D_14 : axst := Eval vm_compute in stepD D_13.
Definition D_15 : axst := Eval vm_compute in stepD D_14.

Definition X_step : axst := Eval vm_compute in stepD D_15.
Definition E_free : axst := Eval vm_compute in leafA_at D_15 free_pc 0.

Definition tiles2_l : list (nat * sv * Z * sv) := ltac2:(tb__ "0|5|
S0S4S4S4S5SbA2M0S29A2M1SbA2M2S1G1SbS1G0S29S1S5SbU1M3S2bS2fA1A4Z8M4A4S42A4S0G2S1G1SbS1G0S29S1S5SbG3S39G4A1A4G4A4S43A4S2G2A1A3A3").

Definition step_facts : list sprop := ltac2:(tb__ "0|1|
S0SdS14S81S12S80S2fSeZ1A1A3S2cA3S0SdSfS39Z20A1M0S2bS2cA1A2S0SdSfG0S2bS2eA1A2S2SdA1A3A3A3").
Definition X_t : axst := Eval vm_compute in ax_setS X_step (optS (tiles_at (ax_S X_step) tiles2_l)).
Definition X_f : axst := ax_add_facts step_facts X_t.
Definition X_m : axst := Eval vm_compute in ax_setS X_f (optS (arr_mat_at (ax_S X_f) 6 (eoff 16) 8)).
Definition s_step : wsub := ltac2:(tb__ "0|4|
S0S4S2aSbA2M0S1S2aSbPacS12S80S2fSeZ1A1A3A4S0G0S1S2aSbPadS11S1eS7bS6bA1A1M1A1A4S0G0S1S2aSbPaeS11Sa4G1A1A1A4S0G0S1S2aSbPafS86SbUeS19S7bS49A1A1M2SeZ0A1M3A4A4S0G0S1S2aSbPb0S86SbU7G2G3A4A4S0G0S1S2aSbPb1S86SbUfG2G3A4A4S2G0A1A3A3A3A3A3A3").

Definition cp0_facts : list sprop := ltac2:(tb__ "0|1|
S0SdS14S81SeZ0A1S2cA3S0SdSfSeZ10A1M0S2bS2cA1A2S0SdSfG0S2bS2eA1A2S2SdA1A3A3A3").
Definition X_cp0f : axst := ax_add_facts cp0_facts X_cp0.
Definition X_cp0m : axst := Eval vm_compute in ax_setS X_cp0f (optS (arr_mat_at (ax_S X_cp0f) 6 (SLit 0) 8)).
Definition s_cp0 : wsub := ltac2:(tb__ "0|4|
S0S4S2aSbA2M0S1S2aSbPacSeZ0A1M1A4S0G0S1S2aSbPadS11S1eS7bS6aA1A1M2A1A4S0G0S1S2aSbPaeS11Sa4G2A1A1A4S0G0S1S2aSbPafS86SbUeS19S7bS37A1A1M3G1A4A4S0G0S1S2aSbPb0S86SbU7G3G1A4A4S0G0S1S2aSbPb1S86SbUfG3G1A4A4S2G0A1A3A3A3A3A3A3").

Definition free_facts : list sprop := ltac2:(tb__ "0|0|
S0SdSfS2cS12S80S2fSeZ1A1A3A2S2SdA1A3").
Definition E_ft : axst := Eval vm_compute in ax_setS E_free (optS (tiles_at (ax_S E_free) tiles2_l)).
Definition E_ff : axst := ax_add_facts free_facts E_ft.
Definition trim_objs (os : list sobj) : list sobj := ltac2:(tb__ "0|2|
S3ScA1M0G0Los;Vos;Vos;ScG0G0G0Ll;R1Vos;ScG0G0G0Ll0;R1Vos;ScG0G0G0Ll1;R1Vos;ScG0G0G0Ll2;R1Vos;ScG0G0G0Ll3;R1Vos;ScG0G0G0Ll4;R1Vos;ScG0G0G0Ll5;R1S0ScReS0ScS13S1bRcA1S1dRcA1S1cRcA1S2S10A1M1S38S2cA1A5S0ScRaS0ScR8S0ScR6S0ScR4S0ScS13S1bR2A1S1dR2A1S1cR2A1G1S24R2A1A5S2ScA1A3A3A3A3A3A3A3ScG0Vos;Ll6;Ls;X3x2Ll5;Lo6;X3x2Ll4;Lo5;X3x2Ll3;Lo4;X3x2Ll2;Lo3;X3x2Ll1;Lo2;X3x2Ll0;Lo1;X3x2Ll;Lo0;X3x2").
Definition E_freeT : axst :=
  Eval vm_compute in mkAX (set_objs (ax_S E_ff) (trim_objs (ss_objs (ax_S E_ff)))) [(vA, SLit 48); (SVar pN, kb16 vKn)] shb.

Definition Pre_f : axst := Pre_free AE_A [] UStopLe.
Definition s_f : wsub := ltac2:(tb__ "0|1|
S0S4S2aSbA2M0S1S2aSbPfS36A4S0G0S1S2aSbPdS2bS2cA1A4Sa3PaS7bS60A1S7bS65A1A3A3A3").
Definition R_f : list sobj := Eval vm_compute in optR (entails_frA E_freeT Pre_f s_f).
Definition T_free : axst := Eval vm_compute in T_afterA Pre_f E_freeT s_f R_f (L_free AE_A [] UStopLe).

Definition vPn : sv := SVar 140.
Definition P_fail_S : sstate := ltac2:(tb__ "0|1|
S17S98S8dS8eS8bA1S0S4S5SbA2M0S1S5SbUaSeZ0A1A4S2G0A1A3A2S8cS15S8SbA1S6ScS0ScS3dS2S10A1A1S0ScS3cS0ScS3eS0ScS47S2ScA1A3A3A3A3S93A3S40Sa8S7A9").
Definition P_fail : axst := mkA P_fail_S X_ra.
Definition ok_facts : list sprop := ltac2:(tb__ "0|0|
S0SdS16P8cZ4A2S0SdS22S14S84S30SeZ0A1A3A1S0SdSfSeZ1000A1S30A2S0SdSfS12S80S30S2bS2eA1A3S11P1eA1A2S0SdSfS30SeS41A1A2S0SdSfSeSa7A1S30A2S2SdA1A3A3A3A3A3A3").
Definition O_new : sobj := ltac2:(tb__ "0|0|
S13S30SeZ0A1S2bS2eA1S2S10A1S38S2cA1A5").
Definition P_ok_S : sstate := ltac2:(tb__ "0|1|
S17S98S8dS8eS8bA1S0S4S5SbA2M0S1S5SbUaS30A4S2G0A1A3A2S8cS15S8SbA1S6ScS0ScS3dS2S10A1A1S0ScS3cS0ScS3eS0ScS61S2ScA1A3A3A3A3S93A3S6SdS71S40A3P8dS7A9").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S95S64S0S4SbSbA2M0S1SbSbS35SeZ30A1A4S0G0S1SbSbS30S2bS2eA1A4S2G0A1A3A3A2").

Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SbSbA2M0S1SbSbS32S2bS2cA1A4S2G0A1A3").
Definition tv1 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SbSbA2M0S1SbSbS11S3aA1S2bS2eA1A4S0G0S1SbSbS32S2bS2cA1A4S2G0A1A3A3").
Definition tv2 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SbSbA2M0S1SbSbS11S3aA1S2bS2eA1A4S2G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SbSbA2M0S1SbSbS30S2bS2eA1A4S2G0A1A3").
Definition bd0 : list bitem := ltac2:(tb__ "0|2|
S0S87S89Z1M0Z0M1S2bS2eA1A3S0S87S88G1Sa2Z2S8aA2G0A3S2S87A1A3A3").
Definition bd1 : list bitem := [BIc 0 KU 1].
Definition ndR (tv : list (sv * sv)) (bd : list bitem) : ndesc := ND tv [] bd.

Definition z0 : sv := SLit 0.

Definition VQ (c : Z) : sv := ltac2:(tb__ "0|0|
S12S82S21S85SeZ20A1S12S82S12S80SeS9fS41Z1A2A1S2cA3S2fA3A3SeVc;A1A3").
Definition cutsE : list edescA := ltac2:(tb__ "0|6|
S0S4S4S7aS7dA2M0S4S29SbA2M1A2M2S1G0G1S1S7aS7dS48S31S3bS4aA2A4S1S29SbZ64S33A4A4S0G2S1G0G1S1S7aS7dS68S31S3bS3fA2A4S1S29SbZ50S33A4M3A4S0G2S1G0G1S1S7aS7dS69S31S4eS3fA2M4A4G3A4S0G2S1G0G1S1S7aS7dS4fG4A4S1S29SbZ46M5S2dZ0A1A4A4S0G2S1G0G1S1S7aS7dS50G4A4S1S29SbG5S2dZ1A1A4A4S0G2S1G0G1S1S7aS7dS57G4A4S1S29SbG5S2dZ3A1A4A4S0G2S1G0G1S1S7aS7dS58G4A4S1S29SbG5S2dZ5A1A4A4S0G2S1G0G1S1S7aS7dS59G4A4S1S29SbG5S2dZ7A1A4A4S0G2S1G0G1S1S7aS7dS5aG4A4S1S29SbG5S2dZ9A1A4A4S0G2S1G0G1S1S7aS7dS5bG4A4S1S29SbG5S2dZbA1A4A4S0G2S1G0G1S1S7aS7dS5cG4A4S1S29SbG5S2dZdA1A4A4S0G2S1G0G1S1S7aS7dS5dG4A4S1S29SbG5S2dZfA1A4A4S0G2S1G0G1S1S7aS7dS5eG4A4S1S29SbG5S2dZ11A1A4A4S0G2S1G0G1S1S7aS7dS51G4A4S1S29SbG5S2dZ13A1A4A4S0G2S1G0G1S1S7aS7dS52G4A4S1S29SbG5S2dZ15A1A4A4S0G2S1G0G1S1S7aS7dS53G4A4S1S29SbG5S2dZ17A1A4A4S0G2S1G0G1S1S7aS7dS54G4A4S1S29SbG5S2dZ19A1A4A4S0G2S1G0G1S1S7aS7dS55G4A4S1S29SbG5S2dZ1bA1A4A4S0G2S1G0G1S1S7aS7dS56G4A4S1S29SbG5S2dZ1dA1A4A4S0G2S1G0G1S1S7aS7dS67S31S75S2S87A1A2A4S1S29SbZ3cS33A4A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|6|
S0S4S4S7aS7dA2M0S4S29SbA2M1A2M2S1G0G1S1S7aS7dS45S31S3bS4aA2A4S1S29SbZ5aS33A4A4S0G2S1G0G1S1S7aS7dS37S31S4eS3fA2M3A4S1S29SbZ4bS33A4A4S0G2S1G0G1S1S7aS7dS49G3A4S1S29SbZ46S2dZ1fA1A4A4S0G2S1G0G1S1S7aS7dS5fG3A4S1S29SbZ41S33A4A4S0G2S1G0G1S1S7aS7dS62S31S3bS2S87A1M4A2A4S1S29SbZ0S33A4M5A4S0G2S1G0G1S1S7aS7dS63S31S76G4A2A4G5A4S2G2A1A3A3A3A3A3A3").

Definition P0_ra (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S90S29S29S90S29S29S90S29S29S91Sa9S4S4S29S29A2M0S29A2S1G0S29S1S29S29R3R2A4R1A4VFF;A3S91Sa0R3SaaQ40S25Vr;PcA2A2M1A2Sa0S9fG1Z30A2S9fR3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2").

Goal entailsA X_m C_0 s_step = true /\ entailsA X_cp0m C_0 s_cp0 = true /\ entailsA E_ff E_freeT [] = true
     /\ call_checkPA E_freeT Pre_f s_f R_f [L_free AE_A [] UStopLe] = true /\ length R_f = 3%nat
     /\ call_checkPA E_m Pre_m s_m R_m [L_malloc_null AE_A [] UStopLe; L_malloc_ok AE_A [] UStopLe] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S92S9S7eS96S8bS46S4bP64S6dS6eA7SaA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_realloc_darr.

