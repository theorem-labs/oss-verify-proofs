(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "nil"; "bool"; "true"; "None"; "false"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sobj"; "cell"; "sprop"; "FcsrFrm0"; "SPUle"; "mkObj"; "mkSS"; "swf"; "DImage"; "DUnknown"; "SAlu"; "SPAlign"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "fc"; "FERR"; "fregs_fw"; "EBUF"; "NPOST_FW"; "O_ferr0"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface"; "D_FP"; "P_ref"; "O_fpstk"; "Pre_ref"; "facts_fp"; "FMT_REF"; "O_ferr2"; "X_ref"; "X_win"; "fp_entry"; "fp_ret"; "objs_fp"; "objs_fp'"; "post_regs_fp"; "reg_fp"; "regs_fp"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "O_got"; "O_rtc"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "O_cflag"; "O_realm"; "O_realv"; "O_rtc3w"; "O_ssp"; "ms16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axwf"; "leafA"; "mkAX"; "mkLeafA"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "add"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "pow"; "sub"; "add"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition fp_entry : Z := 0x4d154.
Definition fp_ret : Z := 0x50a0c.
Definition D_FP : Z := 2560.
Definition FMT_REF : Z := 0x1a7ed.

Definition MSG_REF : list byte := ltac2:(tb__ "0|9|
S31S18S4cQ8M0A1S4bG0A1S1S18Z63S1S18Z6cS1S18Z69M1S1S18Z3aS1S18Z20M2S1S18G1S1S18Z6eS1S18Z70S1S18Z75M3S1S18Z74M4S1S18G2S1S18Z3eS1S18Z3dS1S18G2S1S18Z36M5S1S18Z37S1S18Z31S1S18Z30S1S18Z38M6S1S18G6S1S18G5S1S18Z34S1S18G2S1S18Z62S1S18Z79S1S18G4S1S18Z65M7S1S18Z73M8S1S18Z2cS1S18G2S1S18Z72S1S18G7S1S18Z66S1S18G3S1S18G8S1S18G7S1S18Z64S1S18ZaS2S18A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A4").

Definition O_fpstk : sobj := ltac2:(tb__ "0|0|
S11SbPaA1SaS43S21A1A1SaZ0A1S2SdA1S15A5").

Definition O_ferr2 : sobj := ltac2:(tb__ "0|3|
S11SaZ0M0A1SaS1aA1SaS46S1aZe8A2A1S1SdS19G0Z4M1Z5A3S1SdS19Z60Z8M2G0A3S1SdS19Z58G2S1cA3S1SdS19Z38G2G0A3S1SdS19Z28G2G0A3S1SdS19Z20G2G0A3S1SdS19Z10G2G0A3S1SdS19G2G2G0A3S1SdS19Z88G1S45S44Z2Z40A2Z1A2A3S2SdA1A3A3A3A3A3A3A3A3A3S14A5").
Definition objs_fp : list sobj := ltac2:(tb__ "0|0|
S1ScS23S1ScS1eS1ScS39S1ScS36S1ScS38S1ScS37S1ScS3aS1ScS33S1ScS34S2ScA1A3A3A3A3A3A3A3A3A3").
Definition objs_fp' : list sobj := ltac2:(tb__ "0|0|
S1ScS23S1ScS27S1ScS39S1ScS36S1ScS38S1ScS37S1ScS3aS1ScS33S1ScS34S2ScA1A3A3A3A3A3A3A3A3A3").
Definition facts_fp : list sprop := ltac2:(tb__ "0|2|
S1SeS17PaM0Z4A2S1SeS10SaZ7fff7ff01000A1SbG0A1M1A2S1SeS10G1SaS45S44Z2Z2fA2Z10A2A1A2S1SeS3bZ918A1S2SeA1A3A3A3A3").
Definition X_win : sv * sv := ltac2:(tb__ "0|0|
S7S9S9S16S48SbPaA1SaS43S21A1A1A3SaS21A1A4").
Definition X_ref : list (sv * sv) := ltac2:(tb__ "0|1|
S1S8S9S9A2M0S7S9S9SaZ1a7c0A1SaZ80A1A4S1G0S29S2G0A1A3A3").

Definition reg_fp (a1 a2 : sv) (r : nat) : sv := ltac2:(tb__ "0|1|
S0S9Lr;Vr;SaZ0A1S0S0S9Ln;R1SbPbA1S0S0S9Ln0;R1SbPaA1S0S0S9Ln1;R1SaZ10800A1S0S0S9Ln2;R1SaZ6245b8A1S0S0S9Ln3;R1SbS41S47U3cVr;A2A1A1M0S0S0S9Ln4;R1G0S0S0S9Ln5;R1G0S0S0S9Ln6;R1G0S0S0S9Ln7;R1G0S0S0S9Ln8;R1SaS1aA1S0S0S9Ln9;R1Va1;S0S0S9Ln10;R1Va2;S0G0Ln11;X0x2Ln10;X0x2Ln9;X0x2Ln8;X0x2Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition regs_fp (a1 a2 : sv) : list sv := ltac2:(tb__ "0|0|
S31S0S9S2fVa1;Va2;A2S32U0U20A2A4").
Definition post_reg_fp (a0 : sv) (r : nat) : sv := ltac2:(tb__ "0|1|
S0S9Lr;Vr;SaZ0A1S0S0S9Ln;R1SbPbA1S0S0S9Ln0;R1SbPaA1S0S0S9Ln1;R1SaZ10800A1S0S0S9Ln2;R1SaZ6245b8A1S0S0S9Ln3;R1SbS42P64S41Vr;A1A2A1M0S0S0S9Ln4;R1G0S0S0S9Ln5;R1G0S0S0S9Ln6;R1SbP44A1S0S0S9Ln7;R1SbP45A1S0S0S9Ln8;R1Va0;S0S0S9Ln9;R1G0S0S0S9Ln10;R1G0S0S0S9Ln11;R1G0S0S0S9Ln12;R1G0S0S0S9Ln13;R1G0S0S0S9Ln14;R1G0S0S0S9Ln15;R1G0S0S0S9Ln16;R1SbP4eA1S0S0S9Ln17;R1SbP4fA1S0S0S9Ln18;R1SbP50A1S0S0S9Ln19;R1SbP51A1S0S0S9Ln20;R1SbP52A1S0S0S9Ln21;R1SbP53A1S0S0S9Ln22;R1SbP54A1S0S0S9Ln23;R1SbP55A1S0S0S9Ln24;R1SbP56A1S0S0S9Ln25;R1SbP57A1S0G0Ln26;X0x2Ln25;X0x2Ln24;X0x2Ln23;X0x2Ln22;X0x2Ln21;X0x2Ln20;X0x2Ln19;X0x2Ln18;X0x2Ln17;X0x2Ln16;X0x2Ln15;X0x2Ln14;X0x2Ln13;X0x2Ln12;X0x2Ln11;X0x2Ln10;X0x2Ln9;X0x2Ln8;X0x2Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition post_regs_fp (a0 : sv) : list sv := map (post_reg_fp a0) (seq 0 32).

Definition Pre_ref : axst := ltac2:(tb__ "0|0|
S3fS12S2aS30SaS26A1SaZ4000000A1A2S1bSfS5S9A1S2cS25S4aS6A9S28SaS35A1A3").
Definition P_ref : axst := ltac2:(tb__ "0|0|
S3fS12S2bS2eSaZ26A1A1S1bSfS5S9A1S2dS25S1dS6A9S2S8S9S9A2A1SaS35A1A3").
Definition Posts_ref : list leafA := ltac2:(tb__ "0|0|
S1S3eS40S22S49A2S2S3eA1A3").

Lemma ref_wf : ltac2:(tb__ "0|0|
S20S1fS3S3dS24A1S4A3S20S1fS3S13S3cS24A1A1S4A3S20S1fS3S3dS22A1S4A3S1fS3S13S3cS22A1A1S4A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma MSG_REF_len : length MSG_REF = 38%nat.
Proof. reflexivity. Qed.
