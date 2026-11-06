(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require StrBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require CfgGlueA2 CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require SummaryA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require MuslMemset.

(* [comment removed for export] *)
Module Str_memchrA.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "holds"; "SLit"; "valuation"; "SVar"; "SAlu"; "ss_facts"; "rl"; "rw"; "SPUle"; "SPBranch"; "eval"; "SPNot"; "sobj"; "SPEq"; "FcsrFrm0"; "agree_below"; "mkSS"; "sprop_below"; "ss_next"; "DList"; "cell"; "mkObj"; "@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "prod"; "bool"; "true"; "list"; "None"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA"; "v120"; "mc_state"; "v122"; "tf"; "inv"; "curs"; "r1"; "C3_0"; "BNZ_eq"; "P_ret_0"; "NOZ"; "T_1j"; "T_23"; "T_23w"; "T_b1"; "T_b2"; "T_b3"; "T_f2"; "T_f3"; "s_f2"; "s_f3"; "BNZ_ne"; "BYTE"; "C1_0"; "FirstNul"; "HI"; "Pre_memchr0"; "base_facts"; "c1"; "inc1"; "svals"; "BZ_eq"; "BZ_ne"; "C1M"; "C2_0"; "C84_0"; "O_str"; "X_2"; "X_3e"; "X_3n"; "X_j"; "r8"; "s_1j"; "s_23"; "s_23w"; "s_b1"; "s_b2"; "s_b3"; "C1"; "C2"; "C3"; "C84"; "C84b"; "FUELM"; "Posts_memchr0"; "c8"; "cutpcs_mc"; "inc8"; "C84b_0"; "HZT"; "P_ret"; "WRD"; "cuts_mc"; "exits_mc"; "step1_vals"; "step8_vals"; "vcuts_mc"; "vexits_mc"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "leafA"; "mkLeafA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "two62"; "setregs"; "cut_regs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "modulo"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_get"; "wsub_id_below"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes"; "nthb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_EQ"; "ALU_SLTU"; "ALU_AND"; "ALU_OR"; "ALU_SUB"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA.MCHAddr"; "memchr_ret"; "memchr_L3"; "memchr_J84"; "memchr_L1"; "memchr_L2"; "memchr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA.ZFacts"; "invZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv HasZero StrBytes CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2 CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.

Module MCHAddr.
  Definition memchr_entry : Z := 0xdab04.
  Definition memchr_L1 : Z := 0xdab20.
  Definition memchr_J84 : Z := 0xdab48.
  Definition memchr_L2 : Z := 0xdab78.
  Definition memchr_L3 : Z := 0xdaba4.
  Definition memchr_ret : Z := 0xdabbc.
End MCHAddr.
Import MCHAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition FUELM : nat := 400%nat.

Definition O_str : sobj := ltac2:(tb__ "0|0|
S17S5PcA1S3Z0A1S5P11A1S1aS16A1S15P3A1A5").
Definition base_facts : list sprop := ltac2:(tb__ "0|6|
S18S1SbS94S5P10A1M0S5PeA1M1A3S18S1SaS6S8dG0S3Z8A1M2A3S5P11A1M3A2S18S1SaG2G3A2S18S1SaG3S3S77A1M4A2S18S1SaG1G4A2S18S1SaS3Z1A1S5PcA1M5A2S18S1SaG5G4A2S1aS1A1A3A3A3A3A3A3A3").
Definition Pre_memchr0 : axst := ltac2:(tb__ "0|1|
S96S12S9dS78S7bS18S1cS19S0A2M0S1bS19S0UbS3Z0A1A4S1aG0A1A3A2S76S10S20S0A1S18SeS47S1aSeA1A3S3eS75S22A9S1aS1cS0S0A2A1A2").

Definition C1M : Z := 72340172838076672.
Definition HI : Z := 9259542123273814144.

Definition v120 : sv := SVar 120.
Definition v122 : sv := SVar 122.
Definition curs (e : sv) : sv := SAlu ALU_ADD (SVar 12) e.
Definition inv (c r : sv) : list sprop := ltac2:(tb__ "0|3|
S18S1SaVc;S5P10A1A2S18S1SaS6S8dVc;S3Z8A1A3S5P11A1A2S18S1SaVc;S3S77A1M0A2S18S1SaS5PeA1M1S6S8dVc;Vr;A3M2A2S18S1SaG2G1A2S18S1SaVr;G0A2S1aS1A1A3A3A3A3A3A3").

Definition mc_state (pc : Z) (regs : list (nat * sv)) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|1|
S96S12Vpc;S78S79S75A1S21S1cS19S0A2M0S18G0S1bS19S0UbS3Z0A1A4S1aG0A1A3Vregs;A3A2S76S10S20S0A1S18SeS47S1aSeA1A3S21S1Vfacts;S3eA3Vnx;S22A9S1aS1cS0S0A2A1A2").

Definition C1_0 : axst := ltac2:(tb__ "0|2|
S24S9bS18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S18G0S1bS19S0UcS25A4S18G0S1bS19S0UfS28S6S8dS23S3Z1A1M1A3A1A4S18G0S1bS19S0U10G1A4S1aG0A1A3A3A3A3S1aS1A1P87A4").
Definition C84_0 : axst := ltac2:(tb__ "0|1|
S24S9aS18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S18G0S1bS19S0UcS25A4S18G0S1bS19S0UeS6S90S3Z0A1S25A3A4S1aG0A1A3A3A3S1aS1A1P87A4").
Definition C2_0 : axst := ltac2:(tb__ "0|1|
S24S9cS18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S18G0S1bS19S0UcS25A4S18G0S1bS19S0UdS3S44A1A4S18G0S1bS19S0UeS3S3cA1A4S18G0S1bS19S0UfS3Z0A1A4S18G0S1bS19S0U10S3Z7A1A4S1aG0A1A3A3A3A3A3A3S1aS1A1P87A4").
Definition C3_0 : axst := ltac2:(tb__ "0|1|
S24S99S18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S18G0S1bS19S0UdS25A4S1aG0A1A3A3S1aS1A1P87A4").

Definition C84b_0 : axst := ltac2:(tb__ "0|1|
S24S9aS18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S18G0S1bS19S0UcS25A4S18G0S1bS19S0UeS3Z1A1A4S1aG0A1A3A3A3S1aS1A1P87A4").
Definition C1 : axst := ltac2:(tb__ "0|0|
S7eS27S23S25A2S3aA2").
Definition C84 : axst := ltac2:(tb__ "0|0|
S7eS27S23S25A2S46A2").
Definition C84b : axst := ltac2:(tb__ "0|0|
S7eS27S23S25A2S5dA2").
Definition C2 : axst := ltac2:(tb__ "0|0|
S7eS27S23S25A2S45A2").
Definition C3 : axst := ltac2:(tb__ "0|0|
S7eS27S23S25A2S2aA2").

Definition BYTE (e : sv) : sv := SExt false 8 (SLBytes 3 e 1).
Definition WRD (e : sv) : sv := SLBytes 3 e 8.
Definition BZ_eq (e : sv) : sprop := ltac2:(tb__ "0|0|
SbS8fS39Ve;A1S3Z0A1A3").
Definition BNZ_eq (e : sv) : sprop := ltac2:(tb__ "0|0|
SdSbS8fS39Ve;A1S3Z0A1A3A1").
Definition BNZ_ne (e : sv) : sprop := ltac2:(tb__ "0|0|
SbS8eS39Ve;A1S3Z0A1A3").
Definition BZ_ne (e : sv) : sprop := ltac2:(tb__ "0|0|
SdSbS8eS39Ve;A1S3Z0A1A3A1").
Definition HZT (e : sv) : sv := ltac2:(tb__ "0|1|
S6S91S6S92S6S93S3S44A1S60Ve;A1M0A3G0A3S3S3cA1A3").
Definition NOZ (e : sv) : sprop := ltac2:(tb__ "0|0|
SdSbS8eS5eVe;A1S3S3cA1A3A1").

Definition c1 : sv := ltac2:(tb__ "0|0|
S6S8dS28S23A1S3Z1A1A3").
Definition r1 : sv := SAlu ALU_ADD v122 (SLit (-1)).
Definition c8 : sv := ltac2:(tb__ "0|0|
S6S8dS28S23A1S3Z8A1A3").
Definition r8 : sv := SAlu ALU_ADD v122 (SLit (-8)).
Definition tf (f : sprop) : list sprop := ltac2:(tb__ "0|0|
S18S1Vf;S27S23S25A2A3").

Definition T_b1 : axst := ltac2:(tb__ "0|2|
S24S9bS18S1cS19S0A2M0S1bS19S0UaS3fA4S18G0S1bS19S0UcS29A4S18G0S1bS19S0UfS6S8dS28S6S8dS23S3Z1A1M1A3A1G1A3A4S18G0S1bS19S0U10G1A4S1aG0A1A3A3A3A3S26S2bS23A1A1P87A4").
Definition T_1j : axst := ltac2:(tb__ "0|1|
S24S9aS18S1cS19S0A2M0S1bS19S0UaS3fA4S18G0S1bS19S0UcS29A4S18G0S1bS19S0UeS6S90S3Z0A1S29A3A4S1aG0A1A3A3A3S26S2bS23A1A1P87A4").

Definition T_b2 : axst := ltac2:(tb__ "0|1|
S24S9cS18S1cS19S0A2M0S1bS19S0UaS5aA4S18G0S1bS19S0UcS4cA4S18G0S1bS19S0UdS3S44A1A4S18G0S1bS19S0UeS3S3cA1A4S18G0S1bS19S0UfS3Z0A1A4S18G0S1bS19S0U10S3Z7A1A4S1aG0A1A3A3A3A3A3A3S26S2dS23A1A1P87A4").
Definition T_23 : axst := ltac2:(tb__ "0|1|
S24S99S18S1cS19S0A2M0S1bS19S0UaS3fA4S18G0S1bS19S0UdS29A4S1aG0A1A3A3S26S38S23A1A1P87A4").
Definition T_23w : axst := ltac2:(tb__ "0|1|
S24S99S18S1cS19S0A2M0S1bS19S0UaS5aA4S18G0S1bS19S0UdS4cA4S1aG0A1A3A3S26S2dS23A1A1P87A4").

Definition T_b3 : axst := ltac2:(tb__ "0|1|
S24S99S18S1cS19S0A2M0S1bS19S0UaS3fA4S18G0S1bS19S0UdS29A4S1aG0A1A3A3S26S2bS23A1A1P87A4").

Definition T_f2 : axst := ltac2:(tb__ "0|1|
S24S98S18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S1aG0A1A3S26S43S23A1A1P87A4").
Definition T_f3 : axst := ltac2:(tb__ "0|1|
S24S98S18S1cS19S0A2M0S1bS19S0UaS28S23A1A4S1aG0A1A3S26S42S23A1A1P87A4").

Definition X_j : axst := ltac2:(tb__ "0|2|
S24S98S18S1cS19S0A2M0S1bS19S0UaS3Z0A1M1A4S1aG0A1A3S26SbS8fS6S90G1S25A3G1A3A1P87A4").
Definition X_2 : axst := ltac2:(tb__ "0|2|
S24S98S18S1cS19S0A2M0S1bS19S0UaS3Z0A1M1A4S1aG0A1A3S18S1SbS8fS4cG1A3S26S2dS23A1A1A3P87A4").
Definition X_3e : axst := ltac2:(tb__ "0|2|
S24S98S18S1cS19S0A2M0S1bS19S0UaS3Z0A1M1A4S1aG0A1A3S18S1SdSbS8eS29G1A3A1S26S2bS23A1A1A3P87A4").
Definition X_3n : axst := ltac2:(tb__ "0|2|
S24S98S18S1cS19S0A2M0S1bS19S0UaS3Z0A1M1A4S1aG0A1A3S18S1SdSbS8eS29G1A3A1S26S38S23A1A1A3P87A4").

Definition P_ret_0 : axst := ltac2:(tb__ "0|0|
S96S12S98SaaS0S7aS75A1UaS28S5P8cA1A1A4S76S10S20S0A1S18SeS47S1aSeA1A3S3eP8dS22A9S1aS1cS0S0A2A1A2").
Definition P_ret : axst := ltac2:(tb__ "0|0|
S7eS18S1SfS5P8cA1S5P10A1A2S1aS1A1A3S2cA2").
Definition Posts_memchr0 : list leafA := ltac2:(tb__ "0|0|
S18S6fS70S5fSa9A2S1aS6fA1A3").

Definition cuts_mc : list axst := ltac2:(tb__ "0|0|
S18S6dS3dS18S6dS53S18S6dS56S18S6dS54S18S6dS55S18S6dS57S1aS6dA1A3A3A3A3A3A3").
Definition exits_mc : list axst := ltac2:(tb__ "0|0|
S18S6dS31S18S6dS2eS18S6dS32S18S6dS2fS18S6dS30S18S6dS33S18S6dS34S18S6dS35S18S6dS4bS18S6dS48S18S6dS49S18S6dS4aS1aS6dA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition cutpcs_mc : list Z := ltac2:(tb__ "0|0|
S18S73S9bS18S73S9aS18S73S9cS18S73S99S1aS73A1A3A3A3A3").

Definition s_b1 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS31A1S6cS3aA1A3").
Definition s_1j : wsub := ltac2:(tb__ "0|0|
S97S75S6cS2eA1S6cS46A1A3").
Definition s_b2 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS32A1S6cS45A1A3").
Definition s_23 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS2fA1S6cS2aA1A3").
Definition s_23w : wsub := ltac2:(tb__ "0|0|
S97S75S6cS30A1S6cS2aA1A3").
Definition s_b3 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS33A1S6cS2aA1A3").
Definition s_f2 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS34A1S6cS2cA1A3").
Definition s_f3 : wsub := ltac2:(tb__ "0|0|
S97S75S6cS35A1S6cS2cA1A3").

Lemma ent_b1 : ltac2:(tb__ "0|0|
S67S1dS6eS31S3aS50A3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_1j : ltac2:(tb__ "0|0|
S67S1dS6eS2eS46S4dA3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_b2 : ltac2:(tb__ "0|0|
S67S1dS6eS32S45S51A3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_23 : ltac2:(tb__ "0|0|
S67S1dS6eS2fS2aS4eA3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_23w : ltac2:(tb__ "0|0|
S67S1dS6eS30S2aS4fA3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_b3 : ltac2:(tb__ "0|0|
S67S1dS6eS33S2aS52A3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_f2 : ltac2:(tb__ "0|0|
S67S1dS6eS34S2cS36A3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_f3 : ltac2:(tb__ "0|0|
S67S1dS6eS35S2cS37A3S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_b1 : ltac2:(tb__ "0|0|
S67S1dS8aS50S75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_1j : ltac2:(tb__ "0|0|
S67S1dS8aS4dS75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_b2 : ltac2:(tb__ "0|0|
S67S1dS8aS51S75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_23 : ltac2:(tb__ "0|0|
S67S1dS8aS4eS75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_23w : ltac2:(tb__ "0|0|
S67S1dS8aS4fS75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_b3 : ltac2:(tb__ "0|0|
S67S1dS8aS52S75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_f2 : ltac2:(tb__ "0|0|
S67S1dS8aS36S75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_f3 : ltac2:(tb__ "0|0|
S67S1dS8aS37S75A2S1eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition svals (s : wsub) : list sv := ltac2:(tb__ "0|0|
S72S74S0S89Vs;A1S18S74P78S18S74P7aS18S74P10S18S74P11S18S74PeS1aS74A1A3A3A3A3A3A4").
Definition step1_vals : list sv := ltac2:(tb__ "0|0|
S18S0S6S8dS5P78A1S3Z1A1A3S18S0S6S8dS5P7aA1S3N1A1A3S18S0S5P10A1S18S0S5P11A1S18S0S5PeA1S1aS0A1A3A3A3A3A3").
Definition step8_vals : list sv := ltac2:(tb__ "0|0|
S18S0S6S8dS5P78A1S3Z8A1A3S18S0S6S8dS5P7aA1S3N8A1A3S18S0S5P10A1S18S0S5P11A1S18S0S5PeA1S1aS0A1A3A3A3A3A3").
Lemma vals_b1 : svals s_b1 = step1_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_1j : svals s_1j = step1_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_23 : svals s_23 = step1_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_b3 : svals s_b3 = step1_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_b2 : svals s_b2 = step8_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_23w : svals s_23w = step8_vals. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_f2 : ltac2:(tb__ "0|1|
S67S1cS0S0A2S1bS0S0S89S36P8cA2S89S36P10M0A2A4S1bS0S0S5P78A1S5G0A1A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma vals_f3 : ltac2:(tb__ "0|1|
S67S1cS0S0A2S1bS0S0S89S37P8cA2S89S37P10M0A2A4S1bS0S0S5P78A1S5G0A1A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition FirstNul (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S68S67S73S8cS8Vrho;P3A2M0S80Q40S9Vrho;P10A2A2M1A2Z0M2A3S73S68S82G2R1A2S85R1G1A2A2S69S67S73S8cG0R2A2G2A3A1F_;Fi;A2").

Lemma FirstNul_agree : ltac2:(tb__ "0|1|
S74S4S4SacP10R3A2S11R4R3R2A3S3bR4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof.
  intros n rho rho' Hn (A & B & C) [H1 H2]. unfold FirstNul.
  rewrite <- (A 16%positive Hn), <- B. split; assumption.
Qed.

Lemma two62_mod : ltac2:(tb__ "0|1|
S67S73S86S77S84Z2M0Z40A2A2S84G0Z3eA2A3"). Proof. reflexivity. Qed.
Ltac zholds H := cbn [holds eval branch_taken v120 v122 curs c1 r1 c8 r8] in H; unfold bv_ltu, bv_eqb in H;
  rewrite ?add_lit_val, ?add_val, ?lit_unsigned, ?two62_mod in H; cbn [snorm Z.leb Z.ltb Z.sub Z.add Z.opp] in H;
  repeat match type of H with
    | negb _ = true => apply Bool.negb_true_iff in H
    | ~ negb _ = true => apply Bool.not_true_iff_false in H; apply Bool.negb_false_iff in H
    | Z.ltb _ _ = true => apply Z.ltb_lt in H
    | Z.ltb _ _ = false => apply Z.ltb_ge in H
    | Z.leb _ _ = true => apply Z.leb_le in H
    | Z.eqb _ _ = true => apply Z.eqb_eq in H
    | Z.eqb _ _ = false => apply Z.eqb_neq in H
    end.

Section ZFacts.
Variable rho : valuation.
Let c : Z := bv_unsigned (rw rho 120).
Let r : Z := bv_unsigned (rw rho 122).
Let z : Z := bv_unsigned (rw rho 16).
Let A : Z := bv_unsigned (rw rho 17).
Let n : Z := bv_unsigned (rw rho 14).

Definition invZ : Prop := ltac2:(tb__ "0|3|
S68S82Vc;Vz;A2S68S82S83Vc;Z8M0A2VA;A2S68S82Vc;S84Z2Z3eA2M1A2S68S82Vn;S83Vc;Vr;A2M2A2S68S82G2Vn;A2S68S82Vr;G1A2S68S85Vz;Vn;A2S68S82S83Vz;G0A2VA;A2S68S82VA;G1A2S82Vn;G1A2A2A2A2A2A2A2A2A2A2").

Lemma tf_facts : ltac2:(tb__ "0|0|
S1S71S1S2Vrho;A1S21S1S26R1A1S3eA3A3S68S2Vrho;R2A2Sa5A2F_;Ff;").
Proof using .
  intros f HF. unfold tf, inv, base_facts in HF. cbn [app] in HF.
  repeat match type of HF with Forall _ (_ :: _) => apply Forall_cons_iff in HF as [? HF] end.
  split; [assumption|].
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (urange (rw rho 16)) as R6. pose proof (urange (rw rho 17)) as R7. pose proof (urange (rw rho 14)) as R4.
  unfold invZ. subst c r z A n.
  repeat match goal with H : holds rho _ |- _ => zholds H end.
  change (snorm 8) with 8 in *.
  change (8 mod 2 ^ 64) with 8 in *.
  rewrite Z.mod_small in H1 by lia. rewrite Z.mod_small in H3 by lia. rewrite Z.mod_small in H4 by lia.
  rewrite Z.mod_small in H7 by lia.
  repeat split; lia.
Qed.
End ZFacts.

Lemma inv_intro : ltac2:(tb__ "0|2|
S4S80Q40M0S9R1P78A2A2S73S80G0S9R2P7aA2A2S73S80G0S9R3P10A2A2S73S80G0S9R4P11A2A2S73S80G0S9R5PeA2A2S73S82R5R3A2S82S83R6Z8A2R3A2S82R7S84Z2Z3eA2M1A2S82R4S83R8R7A2A2S82S83R9R8A2R5A2S82R9G1A2S82R8G1A2S71S1S2RdA1S27S23S25A2A3F_;F_;F_;F_;F_;F_;F_;Tn;TA;Tz;Tr;Tc;Frho';").
Proof.
  intros rho' c r z A n H1 H2 H3 H4 H5 H6 H7. subst c r z A n.
  pose proof (urange (rw rho' 120)) as R0. pose proof (urange (rw rho' 122)) as R2.
  pose proof (urange (rw rho' 17)) as R7. pose proof (urange (rw rho' 14)) as R4.
  unfold inv. repeat constructor; cbn [holds eval v120 v122]; rewrite ?add_lit_val, ?add_val, ?lit_unsigned, ?two62_mod;
    change (snorm 8) with 8; rewrite ?Z.mod_small by lia; lia.
Qed.

Lemma rw_sub : ltac2:(tb__ "0|0|
S4S8bS74S67S81Q40A1S9S88R3R2A2R1A2ScR3S89R2R1A2A2A3Fi;Fs;Frho;").
Proof. reflexivity. Qed.
Lemma rl_sub : ltac2:(tb__ "0|0|
S4S8bS67S74S1fS81Q8A1A1F_;S8S88R2R1A2A1S8R2A1A3Fs;Frho;").
Proof. reflexivity. Qed.

Lemma svals_eq : ltac2:(tb__ "0|0|
S8bS0S0S0S0S0S67S1fS0A1S41R6A1S18S0R5S18S0R4S18S0R3S18S0R2S18S0R1S1aS0A1A3A3A3A3A3A3S68S67S0S89R7P78A2R6A3S68S67S0S89R7P7aA2R5A3S68S67S0S89R7P10A2R4A3S68S67S0S89R7P11A2R3A3S67S0S89R7PeA2R2A3A2A2A2A2F_;Fe;Fd;Fc;Fb;Fa;Fs;").
Proof. intros s a b c d e H. unfold svals in H. cbn [map] in H. injection H as -> -> -> -> ->. repeat split; reflexivity. Qed.

Lemma holds_BNZ_eq : ltac2:(tb__ "0|0|
S4S0S6bS2R2S2bR1A1A2S69S67S73S8cS8R2P3A2S80Q40ScR2R1A2A2A2Z0A3A1A2Fe;Frho;").
Proof. intros. unfold BNZ_eq, BYTE. apply holds_BNZ'. Qed.
Lemma holds_BZ_eq : ltac2:(tb__ "0|0|
S4S0S6bS2R2S42R1A1A2S67S73S8cS8R2P3A2S80Q40ScR2R1A2A2A2Z0A3A2Fe;Frho;").
Proof. intros. unfold BZ_eq, BYTE. apply holds_BZ'. Qed.
Lemma holds_BNZ_ne : ltac2:(tb__ "0|0|
S4S0S6bS2R2S38R1A1A2S69S67S73S8cS8R2P3A2S80Q40ScR2R1A2A2A2Z0A3A1A2Fe;Frho;").
Proof. intros. unfold BNZ_ne, BYTE. apply holds_BNZ. Qed.
Lemma holds_BZ_ne : ltac2:(tb__ "0|0|
S4S0S6bS2R2S43R1A1A2S67S73S8cS8R2P3A2S80Q40ScR2R1A2A2A2Z0A3A2Fe;Frho;").
Proof. intros. unfold BZ_ne, BYTE. apply holds_BZ. Qed.
Lemma holds_NOZ_mc : ltac2:(tb__ "0|0|
S4S0S2R2S2dR1A1A2S19Sa4R1U8A2S69S67S73S8cS8R5P3A2S83S80Q40ScR5R4A2A2S87R2A1A2A2Z0A3A1F_;Fk;F_;Fe;Frho;").
Proof.
  intros rho e H. apply StrBytes.holds_NOZ. unfold NOZ, HZT in H. unfold StrBytes.NOZ.
  change (StrBytes.WRD e) with (WRD e). fold C1M HI.
  cbn [holds branch_taken] in H |- *. destruct (bv_eqb _ _); [reflexivity|]. exfalso. apply H. reflexivity.
Qed.

Section WithFirstNul.
Variable rho0 : valuation.
Hypothesis FN : FirstNul rho0.
Let G : valuation -> Prop := ltac2:(tb__ "0|0|
S4S11S75Vrho0;R1A3Lrho;").

Lemma G_FN : ltac2:(tb__ "0|0|
S4VG;R1A1S3bR2A1F_;Frho;").
Proof using FN. intros rho Hg. eapply FirstNul_agree; [| exact Hg | exact FN]. reflexivity. Qed.
Lemma G_trans : ltac2:(tb__ "0|0|
S4S4VG;R2A1S11S75R3R2A3VG;R3A1F_;F_;Fr2;Fr1;").
Proof using rho0. intros r1 r2 H1 H2. eapply agree_below_trans; eauto. Qed.

Lemma glue_step1 : ltac2:(tb__ "0|1|
S8bS1S4S67S1fS0A1S41R3A1S63A3S4S2R1R4A2S69S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0M0A3A1F_;Frho;VG;R3A1S71S1S2R4A1S7S6cS24G0S1aS1cS19S0A2A1S26R5A1P87A4A1A1A3S71S1S2S88R5R7A2A1S27S23S25A2A3F_;F_;F_;F_;Frho;Ff;Fs;").
Proof using FN.
  intros s f rho Hs Hf Hg HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  destruct (tf_facts rho f HF) as [Hff Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1]. pose proof (Hf rho Hff) as NZ.
  destruct (svals_eq s _ _ _ _ _ Hs) as (E120 & E122 & E16 & E17 & E14).
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_step (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  apply inv_intro; rewrite !rw_sub, ?E120, ?E122, ?E16, ?E17, ?E14; cbn [eval];
    rewrite ?add_lit_val; cbn [snorm Z.leb]; change (snorm 1) with 1; change (snorm (-1)) with (-1);
    rewrite ?Z.mod_small by lia; lia.
Qed.

Lemma glue_step8 : ltac2:(tb__ "0|0|
S8bS4S67S1fS0A1S41R2A1S64A3VG;R2A1S71S1S2R3A1S7S6cS24Z0S1aS1cS19S0A2A1S26S2dS23A1A1P87A4A1A1A3S71S1S2S88R4R5A2A1S27S23S25A2A3F_;F_;F_;Frho;Fs;").
Proof using FN.
  intros s rho Hs Hg HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  destruct (tf_facts rho _ HF) as [Hff Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1].
  pose proof (holds_NOZ_mc rho v120 Hff) as NZ. cbn [eval v120] in NZ.
  destruct (svals_eq s _ _ _ _ _ Hs) as (E120 & E122 & E16 & E17 & E14).
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_word (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  apply inv_intro; rewrite !rw_sub, ?E120, ?E122, ?E16, ?E17, ?E14; cbn [eval];
    rewrite ?add_lit_val; change (snorm 8) with 8; change (snorm (-8)) with (-8);
    rewrite ?Z.mod_small by lia; lia.
Qed.

Lemma mc_facts : ltac2:(tb__ "0|2|
S73S1fS1cS19S0A2M0A1S1fS1A1M1S74S67G1S7S6cS24R4R3R2R1A4A1A1S7S6cS24Z0S1aG0A1R2P87A4A1A1A3Fnx;FF;Fregs;Fpc;").
Proof using . reflexivity. Qed.

Lemma BNZ_eq_120 : ltac2:(tb__ "0|0|
S4S2R1S2bS23A1A2S69S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0A3A1F_;Frho;").
Proof using . intros rho H. apply holds_BNZ_eq in H. exact H. Qed.
Lemma BNZ_ne_120 : ltac2:(tb__ "0|0|
S4S2R1S38S23A1A2S69S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0A3A1F_;Frho;").
Proof using . intros rho H. apply holds_BNZ_ne in H. exact H. Qed.

Lemma glue_b1 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS31A1A1A3S71S1S2S88R3S50A2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_b1. rewrite mc_facts. apply glue_step1; [exact vals_b1 | exact BNZ_eq_120]. Qed.
Lemma glue_1j : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS2eA1A1A3S71S1S2S88R3S4dA2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_1j. rewrite mc_facts. apply glue_step1; [exact vals_1j | exact BNZ_eq_120]. Qed.
Lemma glue_23 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS2fA1A1A3S71S1S2S88R3S4eA2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_23. rewrite mc_facts. apply glue_step1; [exact vals_23 | exact BNZ_ne_120]. Qed.
Lemma glue_b3 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS33A1A1A3S71S1S2S88R3S52A2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_b3. rewrite mc_facts. apply glue_step1; [exact vals_b3 | exact BNZ_eq_120]. Qed.
Lemma glue_b2 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS32A1A1A3S71S1S2S88R3S51A2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_b2. rewrite mc_facts. apply glue_step8. exact vals_b2. Qed.
Lemma glue_23w : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS30A1A1A3S71S1S2S88R3S4fA2A1S27S23S25A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_23w. rewrite mc_facts. apply glue_step8. exact vals_23w. Qed.

Lemma glue_found : ltac2:(tb__ "0|5|
S8bS1S4S67S1cS0S0A2S1bS0S0S89R3P8cM0A2S89R3P10M1A2A4S1bS0S0S5P78M2A1S5G1A1M3A4A3S4S2R1R4A2S67S73S8cS8R2P3A2S80Q40S9R2G2A2A2A2Z0M4A3F_;Frho;VG;R3A1S71S1S2R4A1S7S6cS24G4S1aS1cS19S0A2A1S26R5A1P87A4A1A1A3S71S1S2S88R5R7A2A1S18S1SfS5G0A1G3A2S1aS1A1A3A3F_;F_;F_;F_;Frho;Ff;Fs;").
Proof using FN.
  intros s f rho Hs Hf Hg HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  destruct (tf_facts rho f HF) as [Hff Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1]. pose proof (Hf rho Hff) as ZB.
  injection Hs as E140 E16.
  pose proof (fn_found (rl rho 3) (bv_unsigned (rw rho 16)) FN1 (bv_unsigned (rw rho 120)) ltac:(pose proof (urange (rw rho 120)); lia) ltac:(lia) ZB) as EQ.
  constructor; [|constructor]. cbn [holds eval]. rewrite !rw_sub, E140, E16. cbn [eval].
  apply bv_eq. exact EQ.
Qed.
Lemma BZ_ne_120 : ltac2:(tb__ "0|0|
S4S2R1S43S23A1A2S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0A3F_;Frho;").
Proof using . intros rho H. apply holds_BZ_ne in H. exact H. Qed.
Lemma BZ_eq_120 : ltac2:(tb__ "0|0|
S4S2R1S42S23A1A2S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0A3F_;Frho;").
Proof using . intros rho H. apply holds_BZ_eq in H. exact H. Qed.
Lemma glue_f2 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS34A1A1A3S71S1S2S88R3S36A2A1S18S1SfS5P8cA1S5P10A1A2S1aS1A1A3A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_f2. rewrite mc_facts. apply glue_found; [exact vals_f2 | exact BZ_ne_120]. Qed.
Lemma glue_f3 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS35A1A1A3S71S1S2S88R3S37A2A1S18S1SfS5P8cA1S5P10A1A2S1aS1A1A3A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_f3. rewrite mc_facts. apply glue_found; [exact vals_f3 | exact BZ_eq_120]. Qed.

Lemma contra_j : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS4bA1A1A3S6aF_;F_;Frho;").
Proof using rho0.
  intros rho Hg HF. unfold X_j in HF. rewrite mc_facts in HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  destruct (tf_facts rho _ HF) as [H Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  cbn [holds eval branch_taken v122] in H.
  destruct (sltu0_cases (rw rho 122)) as [[EE BB]|[EE BB]]; rewrite EE in H.
  - vm_compute in H. discriminate.
  - lia.
Qed.
Lemma contra_2 : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS48A1A1A3S6aF_;F_;Frho;").
Proof using FN.
  intros rho Hg HF. unfold X_2 in HF. rewrite mc_facts in HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  apply Forall_cons_iff in HF as [H8 HF].
  destruct (tf_facts rho _ HF) as [Hn Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1].
  pose proof (holds_NOZ_mc rho v120 Hn) as NZ. cbn [eval v120] in NZ.
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_word (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  zholds H8. change (snorm (-8)) with (-8) in H8. change (0 mod 2 ^ 64) with 0 in H8.
  assert (bv_unsigned (rw rho 122) >= 9) by lia.
  rewrite Z.mod_small in H8 by lia. lia.
Qed.
Lemma contra_3 : ltac2:(tb__ "0|1|
S1S4S4S2R1R3A2S69S67S73S8cS8R2P3A2S80Q40S9R2P78A2A2A2Z0M0A3A1F_;Frho;VG;R2A1S71S1S2R3A1S18S1SdSbS8eS29S3G0A1A3A1S7S6cS24G0S1aS1cS19S0A2A1S26R4A1P87A4A1A1A3A3S6aF_;F_;F_;Frho;Ff;").
Proof using FN.
  intros f rho Hf Hg HF. cbn [ss_facts ax_S mc_state mkA] in HF.
  apply Forall_cons_iff in HF as [H1 HF].
  destruct (tf_facts rho _ HF) as [Hn Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1]. pose proof (Hf rho Hn) as NZ.
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_step (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  zholds H1. change (snorm (-1)) with (-1) in H1. change (0 mod 2 ^ 64) with 0 in H1.
  assert (bv_unsigned (rw rho 122) >= 2) by lia.
  rewrite Z.mod_small in H1 by lia. lia.
Qed.
Lemma contra_3e : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS49A1A1A3S6aF_;F_;Frho;").
Proof using FN. intros rho. unfold X_3e. rewrite mc_facts. apply contra_3. exact BNZ_eq_120. Qed.
Lemma contra_3n : ltac2:(tb__ "0|0|
S4VG;R1A1S71S1S2R2A1S7S6cS4aA1A1A3S6aF_;F_;Frho;").
Proof using FN. intros rho. unfold X_3n. rewrite mc_facts. apply contra_3. exact BNZ_ne_120. Qed.

End WithFirstNul.

Lemma inv_below : ltac2:(tb__ "0|0|
S67S1dSa3S1S13S14S6cS3aA1A1A1S27S23S25A2A3S1eA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma post_below : ltac2:(tb__ "0|0|
S67S1dSa3S1S13S14S6cS2cA1A1A1S18S1SfS5P8cA1S5P10A1A2S1aS1A1A3A3S1eA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition inc1 : sv := SAlu ALU_ADD v120 (SLit 1).
Definition inc8 : sv := SAlu ALU_ADD v120 (SLit 8).
Definition vcuts_mc : list vnodeA := ltac2:(tb__ "0|1|
S18S7cS7dS3dZ14S3Z0A1A3S18S7cS7dS53ZaS23A3S18S7cS7dS56Z8M0S23A3S18S7cS7dS54Z6S23A3S18S7cS7dS55Z4S23A3S18S7cS7dS57G0S23A3S1aS7cA1A3A3A3A3A3A3").
Definition vexits_mc : list vnodeA := ltac2:(tb__ "0|3|
S18S7cS7dS31ZcM0S40A3S18S7cS7dS2eG0S40A3S18S7cS7dS32G0S5cA3S18S7cS7dS2fG0S40A3S18S7cS7dS30G0S5cA3S18S7cS7dS33G0S40A3S18S7cS7dS34Z1M1S23A3S18S7cS7dS35G1S23A3S18S7cS7dS4bZ0M2S23A3S18S7cS7dS48G2S23A3S18S7cS7dS49G2S23A3S18S7cS7dS4aG2S23A3S1aS7cA1A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma echeck_mc : ltac2:(tb__ "0|0|
S67S1dSabS95S58S5bS75S65S66A6S1eA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_mc : ltac2:(tb__ "0|0|
S67S1dS7fS95S58S5bS75S61S62A6S1eA3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc cuts_mc exits_mc eq_refl eq_refl echeck_mc). Qed.

Theorem memchr0_sum : ltac2:(tb__ "0|0|
Sa8OF_;Sa0S4S1fS81Q40A1A1Sa2S95R4R3A3Sa1S95S75R4A3S3bR4A1Sa7S95R7S9fS95R6S3dR5R4A5S9eS95R6S75R5R4S59A6A4F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HFN.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_memchr0 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELM cutpcs_mc NF cuts_mc exits_mc (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_memchr0) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - exact HstG.
  - exact check_mc.
  - intros E rhoE HinE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_b1 C1_0 (inv v120 v122) s_b1 tp);
        [right; left; reflexivity | exact ent_b1 | exact id_b1 | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_b1 rho HFN r Hg HF)].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_1j C84_0 (inv v120 v122) s_1j tp);
        [right; right; left; reflexivity | exact ent_1j | exact id_1j | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_1j rho HFN r Hg HF)].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_b2 C2_0 (inv v120 v122) s_b2 tp);
        [right; right; right; left; reflexivity | exact ent_b2 | exact id_b2 | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_b2 rho HFN r Hg HF)].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_23 C3_0 (inv v120 v122) s_23 tp);
        [right; right; right; right; left; reflexivity | exact ent_23 | exact id_23 | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_23 rho HFN r Hg HF)].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_23w C3_0 (inv v120 v122) s_23w tp);
        [right; right; right; right; left; reflexivity | exact ent_23w | exact id_23w | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_23w rho HFN r Hg HF)].
    + apply (exit_reenterA segs ok _ NF cuts_mc _ T_b3 C3_0 (inv v120 v122) s_b3 tp);
        [right; right; right; right; left; reflexivity | exact ent_b3 | exact id_b3 | exact HstG | exact inv_below | intros r tp' tr md [Hg _] HF; exact (glue_b3 rho HFN r Hg HF)].
    + apply (exit_post_GA segs ok J NF rho cuts_mc Posts_memchr0 T_f2 P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f2 tp);
        [left; reflexivity | exact ent_f2 | exact id_f2 | exact Hst | exact post_below | intros r Hg HF; exact (glue_f2 rho HFN r Hg HF)].
    + apply (exit_post_GA segs ok J NF rho cuts_mc Posts_memchr0 T_f3 P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f3 tp);
        [left; reflexivity | exact ent_f3 | exact id_f3 | exact Hst | exact post_below | intros r Hg HF; exact (glue_f3 rho HFN r Hg HF)].
    + apply (exit_contraA segs ok _ X_j). intros r tp' tr md [Hg _] HF. exact (contra_j rho r Hg HF).
    + apply (exit_contraA segs ok _ X_2). intros r tp' tr md [Hg _] HF. exact (contra_2 rho HFN r Hg HF).
    + apply (exit_contraA segs ok _ X_3e). intros r tp' tr md [Hg _] HF. exact (contra_3e rho HFN r Hg HF).
    + apply (exit_contraA segs ok _ X_3n). intros r tp' tr md [Hg _] HF. exact (contra_3n rho HFN r Hg HF).
  - left; reflexivity.
Qed.

Lemma meas_reenter : ltac2:(tb__ "0|2|
S4S8bS0S1fS0A1M0S67G0S41R3A1S18S0R2R1A3A3S82S80Q40M1ScR5R3A2A2S80G1ScS88R5R4A2S23A2A2A2F_;Frest;Fv;Fs;Frho;").
Proof.
  intros rho s v rest H. unfold svals in H. cbn [map] in H. injection H as H _.
  cbn [eval v120]. rewrite rw_sub, H. lia.
Qed.

Theorem memchr0_sum_ex : ltac2:(tb__ "0|0|
Sa0S4S1fS81Q40A1A1Sa1S95S75R3A3S3bR3A1Sa6S95S9fS95R5S3dR4R3A5S9eS95R5S75R4R3S59A6A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HFN.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_memchr0 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_memchr0 with (vna_state (mkVNA Pre_memchr0 20 (SLit 0))).
  apply (cfg_complete_autoIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_memchr0) tp).
  - exact HstG.
  - intros n Hin. unfold vcuts_mc in Hin. repeat (destruct Hin as [<-|Hin]; [cbv; congruence|]). destruct Hin.
  - exact echeck_mc.
  - intros E rhoE HinE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_b1 12 inc1) (mkVNA C1 10 v120) (inv v120 v122) C1_0 s_b1 tp);
        [right; left; reflexivity | reflexivity | exact ent_b1 | exact id_b1 | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_b1 rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_b1 _ _ vals_b1) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_1j 12 inc1) (mkVNA C84 8 v120) (inv v120 v122) C84_0 s_1j tp);
        [right; right; left; reflexivity | reflexivity | exact ent_1j | exact id_1j | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_1j rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_1j _ _ vals_1j) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_b2 12 inc8) (mkVNA C2 6 v120) (inv v120 v122) C2_0 s_b2 tp);
        [right; right; right; left; reflexivity | reflexivity | exact ent_b2 | exact id_b2 | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_b2 rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_b2 _ _ vals_b2) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_23 12 inc1) (mkVNA C3 4 v120) (inv v120 v122) C3_0 s_23 tp);
        [right; right; right; right; left; reflexivity | reflexivity | exact ent_23 | exact id_23 | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_23 rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_23 _ _ vals_23) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_23w 12 inc8) (mkVNA C3 4 v120) (inv v120 v122) C3_0 s_23w tp);
        [right; right; right; right; left; reflexivity | reflexivity | exact ent_23w | exact id_23w | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_23w rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_23w _ _ vals_23w) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA T_b3 12 inc1) (mkVNA C3 4 v120) (inv v120 v122) C3_0 s_b3 tp);
        [right; right; right; right; left; reflexivity | reflexivity | exact ent_b3 | exact id_b3 | exact HstG | exact inv_below
        | intros r tp' tr md [Hg _] HF; split; [exact (glue_b3 rho HFN r Hg HF) | right; split; [exact (meas_reenter r s_b3 _ _ vals_b3) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_post_IA segs J NF rho vcuts_mc Posts_memchr0 (mkVNA T_f2 1 v120) P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f2 tp);
        [left; reflexivity | exact ent_f2 | exact id_f2 | exact Hst | exact post_below | intros r Hg HF; exact (glue_f2 rho HFN r Hg HF)].
    + apply (eexit_post_IA segs J NF rho vcuts_mc Posts_memchr0 (mkVNA T_f3 1 v120) P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f3 tp);
        [left; reflexivity | exact ent_f3 | exact id_f3 | exact Hst | exact post_below | intros r Hg HF; exact (glue_f3 rho HFN r Hg HF)].
    + apply (eexit_contraA segs _ X_j). intros r tp' tr md [Hg _] HF. exact (contra_j rho r Hg HF).
    + apply (eexit_contraA segs _ X_2). intros r tp' tr md [Hg _] HF. exact (contra_2 rho HFN r Hg HF).
    + apply (eexit_contraA segs _ X_3e). intros r tp' tr md [Hg _] HF. exact (contra_3e rho HFN r Hg HF).
    + apply (eexit_contraA segs _ X_3n). intros r tp' tr md [Hg _] HF. exact (contra_3n rho HFN r Hg HF).
  - left; reflexivity.
Qed.
End Str_memchrA.

(* [comment removed for export] *)
Module Icpt_region.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "app"; "bool"; "true"; "prod"; "andb"; "None"; "false"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SLit"; "SPUle"; "cell"; "SPUlt"; "sobj"; "mkCell"; "SPAlign"; "FcsrFrm0"; "SPEq"; "mkSS"; "DUnknown"; "SAlu"; "mkObj"; "SPBranch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "cur"; "shp"; "add"; "gd"; "gu"; "pae"; "vB"; "pab"; "vL"; "F_ae"; "miz_regs"; "miz_state"; "shpk"; "F_ab"; "cnt"; "g8"; "vN"; "E_Ee"; "E_Pe"; "E_We"; "beg"; "s_Ee"; "s_Pe"; "s_We"; "CE_0"; "CP_0"; "CW_0"; "E_Eb"; "E_Pb"; "E_Wb"; "O_rtc2"; "O_stk"; "X_rip"; "base_facts"; "endd"; "stk_cells"; "C0"; "CE"; "CP"; "CW"; "FUEL"; "P_ret"; "RA_MIZ"; "cutpcs_rip"; "g_facts"; "s_Eb"; "s_Pb"; "s_Wb"; "vO"; "F_E"; "F_P"; "F_W"; "KHME"; "cuts_rip"; "exits_rip"; "lastt"; "regs_C0"; "stk_cells8"; "vcuts_rip"; "vexits_rip"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "post_regs"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.RegionAddr"; "miz_epi"; "miz_pro"; "miz_word"; "rip_C0"; "rip_ret"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "mkA"; "segs"; "ACEIL"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module RegionAddr.
  Definition rip_entry : Z := 0x600d8.
  Definition rip_C0 : Z := 0x601cc.
  Definition rip_ret : Z := 0x60278.
  Definition miz_pro : Z := 0x7040c.
  Definition miz_word : Z := 0x70428.
  Definition miz_epi : Z := 0x70444.
End RegionAddr.
Import RegionAddr.

Definition HSE : Z := 0x10007fff8000.
Definition KHME : Z := 0x7fffffffffff.
Definition M8 : Z := 18446744073709551608.

Definition O_rtc2 : sobj := ltac2:(tb__ "0|3|
S1bSfZ0A1M0SfZeeda0A1M1SfZeedb8A1S0S11S14G1Z8M2SfS51A1A3S0S11S14SfZeeda8A1G2G0A3S0S11S14SfZeedb0A1G2G0A3S3S11A1A3A3A3S19A5").

Definition vB := SVar 15. Definition vL := SVar 16. Definition vO := SVar 17. Definition vN := SVar 18.
Definition gu := SVar 120. Definition gd := SVar 121.
Definition add (a b : sv) : sv := SAlu ALU_ADD a b.
Definition g8 (g : sv) : sv := SAlu ALU_SLL g (SLit 3).
Definition shp (g : sv) : sv := add g shb.
Definition beg : sv := add vB vO.
Definition endd : sv := add vN beg.
Definition X_rip : list (sv * sv) := ltac2:(tb__ "0|1|
S0S7ScScA2M0S1ScScS23S25A4S3G0A1A3").

Definition stk_cells : list cell := ltac2:(tb__ "0|1|
S0S11S14SfN38A1Z8M0SeP29A1A3S0S11S14SfN30A1G0SeP28A1A3S0S11S14SfN28A1G0SeP27A1A3S0S11S14SfN20A1G0SeP26A1A3S0S11S14SfN18A1G0SeP1dA1A3S0S11S14SfN10A1G0SeP1cA1A3S0S11S14SfN8A1G0SePbA1A3S3S11A1A3A3A3A3A3A3A3").
Definition O_stk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1bSePaA1SfN50A1SfZ0A1Vcells;S19A5").

Definition base_facts : list sprop := ltac2:(tb__ "0|4|
S0SdS10S1fS4dS2dA2S25A2S0SdS10S4dS25A2S0SdS10S2dS25A2S0SdS10S25SfS68Z2M0Z28A2A1A2S0SdS10SfZ1A1S2dA2S0SdS10SfZ1000A1S23A2S0SdS10S1fS23S25A2SfS69S68G0Z2fA2Z8A2A1M1A2S0SdS10S23G1A2S0SdS15PfZ3A2S0SdS15PaM2Z4A2S0SdS10SfS76A1SeG2A1M3A2S0SdS10G3SfS68G0Z3fA2A1A2S3SdA1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition g_facts : list sprop := ltac2:(tb__ "0|4|
S0SdS10S31S2cS21A1M0A2S0SdS10G0S1fS31SfZ7A1A2A2S0SdS10S2cS20A1M1S3fA2S0SdS10S1fS3fSfN7A1A2G1A2S0SdS10S23G0A2S0SdS10S23G1A2S0SdS10G1S1fS23S25A2A2S0SdS10S21SfS69S68Z2M2Z3dA2Z1A2A1M3A2S0SdS10S20G3A2S0SdS10S20S1fS21SfS68G2Z25A2A1A2A2S3SdA1A3A3A3A3A3A3A3A3A3A3").

Definition regs_C0 : list sv := ltac2:(tb__ "0|1|
S65S66S0S7S2ScA2M0S1S2ScU1SfS70A1A4S0G0S1S2ScU2S1fSePaA1SfN40A1A2A4S0G0S1S2ScU8S31A4S0G0S1S2ScU9S2dA4S0G0S1S2ScUaS1eS20A1A4S0G0S1S2ScU12S3fA4S0G0S1S2ScU13S1eS21A1A4S0G0S1S2ScU14SeP7aA1A4S0G0S1S2ScU15SfZee0b8A1A4S0G0S1S2ScU5SeP7bA1A4S0G0S1S2ScU6SeP7cA1A4S0G0S1S2ScU7SeP7dA1A4S0G0S1S2ScUbSeP7eA1A4S0G0S1S2ScUcSeP7fA1A4S0G0S1S2ScUdSeP80A1A4S0G0S1S2ScUeSeP81A1A4S0G0S1S2ScUfSeP82A1A4S0G0S1S2ScU10SeP83A1A4S0G0S1S2ScU11SeP84A1A4S0G0S1S2ScU1cSeP85A1A4S0G0S1S2ScU1dSeP86A1A4S0G0S1S2ScU1eSeP87A1A4S0G0S1S2ScU1fSeP88A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition C0 : axst := ltac2:(tb__ "0|0|
S74S18S70S55S64S16S9ScA1S4S13S0S13S3cS40A1S0S13S3bS3S13A1A3A3S73A3S4SdS49S3eA3P89SaA9S3dA2").

Definition RA_MIZ : Z := 0x6024c.
Definition lastt : sv := add endd (SLit (-1)).
Definition stk_cells8 : list cell := ltac2:(tb__ "0|0|
S0S11S14SfN48A1Z8SfS47A1A3S40A3").
Definition pab := SVar 140. Definition pae := SVar 141. Definition cur := SVar 142. Definition cnt := SVar 143.
Definition shpk (g : sv) (k : Z) : sv := ltac2:(tb__ "0|0|
S1fVg;SfS6aS77Vk;A2A1A2").

Definition miz_regs (a0 a2 a3 a4 a5 a6 : sv) : list sv := ltac2:(tb__ "0|1|
S65S66S0S7S2ScA2M0S1S2ScU1SfS47A1A4S0G0S1S2ScU2S1fSePaA1SfN50A1A2A4S0G0S1S2ScU5SeP7bA1A4S0G0S1S2ScU6SeP7cA1A4S0G0S1S2ScU7SeP7dA1A4S0G0S1S2ScU8S31A4S0G0S1S2ScU9S2dA4S0G0S1S2ScUaVa0;A4S0G0S1S2ScUbSfZ0A1A4S0G0S1S2ScUcVa2;A4S0G0S1S2ScUdVa3;A4S0G0S1S2ScUeVa4;A4S0G0S1S2ScUfVa5;A4S0G0S1S2ScU10Va6;A4S0G0S1S2ScU11SeP84A1A4S0G0S1S2ScU12S54A4S0G0S1S2ScU13S1eS21A1A4S0G0S1S2ScU14SeP7aA1A4S0G0S1S2ScU15SfZee0b8A1A4S0G0S1S2ScU1cSeP85A1A4S0G0S1S2ScU1dSeP86A1A4S0G0S1S2ScU1eSeP87A1A4S0G0S1S2ScU1fSeP88A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition miz_state (pc : Z) (regs : list sv) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
S74S18Vpc;Vregs;S64S16S9ScA1S4S13S0S13S3cS56A1S0S13S3bS3S13A1A3A3S73A3S4SdVfacts;S4SdS49S3eA3A3Vnx;SaA9S3dA2").

Definition F_ab : list sprop := ltac2:(tb__ "0|2|
S0SdS10S24S1fS21SfZ7A1M0A2M1A2S0SdS10G1S1fS24G0A2A2S0SdS15P8cZ3A2S3SdA1A3A3A3").
Definition F_ae : list sprop := ltac2:(tb__ "0|0|
S0SdS10S22S20A2S0SdS10S20S1fS22SfZ7A1A2A2S0SdS15P8dZ3A2S3SdA1A3A3A3").

Definition CW_0 : axst := ltac2:(tb__ "0|0|
S28S6fS27S1eS21A1S1eS22A1SeP90A1S1eS20A1S1eS1dA1SeP91A1A6S4SdS2aS26A3P96A4").
Definition F_W : list sprop := ltac2:(tb__ "0|1|
S0SdS10S23S2cS1dA1M0A2S0SdS10S1fG0SfZ40A1A2S1fS23S25A2A2S0SdS17G0G0A2S0SdS10S1dSfS69S68Z2Z3dA2Z1A2A1A2S0SdS10S21S1dA2S0SdS12S1dS22A2S0SdS15P8eZ3A2S0SdS12S1dS20A2S3SdA1A3A3A3A3A3A3A3A3").
Definition CW : axst := ax_add_facts F_W CW_0.

Definition CP_0 : axst := ltac2:(tb__ "0|0|
S28S6eS27S1eS21A1S1eS22A1S29S1dZ1A2S1eS20A1S1eS24A1SeP91A1A6S4SdS2aS26A3P96A4").
Definition F_P : list sprop := ltac2:(tb__ "0|1|
S0SdS10S23S2cS1dA1M0A2S0SdS10S1fG0SfZ8A1A2S1fS23S25A2A2S0SdS17G0G0A2S0SdS10S1dSfS69S68Z2Z3dA2Z1A2A1A2S0SdS10S21S1dA2S0SdS12S1dS24A2S0SdS12S1dS20A2S3SdA1A3A3A3A3A3A3A3").
Definition CP : axst := ax_add_facts F_P CP_0.

Definition CE_0 : axst := ltac2:(tb__ "0|0|
S28S6dS27SeP93A1S1eS1dA1SeP90A1S2bSeP92A1SeP91A1A6S26P96A4").
Definition F_E : list sprop := ltac2:(tb__ "0|3|
S0SdS10S23S2cS1dA1M0A2S0SdS10S1fG0SfZ8A1A2S1fS23S25A2A2S0SdS17G0G0A2S0SdS10S1dSfS69S68Z2Z3dA2Z1M1A2A1A2S0SdS10S1fS1dS2bA2M2S20A2S0SdS10S20G2A2S0SdS10SfG1A1S2bA2S0SdS10S2bSfZ7A1A2S0SdS12S1dS20A2S3SdA1A3A3A3A3A3A3A3A3A3").
Definition CE : axst := ax_add_facts F_E CE_0.

Definition P_ret : axst := ltac2:(tb__ "0|1|
S74S18S71S65S67S63A1S0S7S2ScA2M0S1S2ScUaSfZ0A1A4S3G0A1A3A2S64S16S9ScA1S4S13S0S13S3cS40A1S0S13S3bS3S13A1A3A3S73A3S3eP8cSaA9S3dA2").

Definition E_Pe : axst := ltac2:(tb__ "0|0|
S28S6eS27S1eS21A1S1eS22A1S29S21Z1A2S1eS20A1S1eS24A1SeP91A1A6S4SdS2aS4SdS26S0SdS12S21S20A2S0SdS12S21S24A2S3SdA1A3A3A3A3P96A4").
Definition E_Pb : axst := ltac2:(tb__ "0|2|
S28S6eS27S1eS21A1S1eS22A1S29S1dZ2A2S1eS20A1S1eS24A1S29S1dZ1M0A2A6S4SdS4fS4SdS2aS4SdS26S0SdS12S1fS1dSfG0A1A2M1S24A2S0SdS12G1S20A2S3SdA1A3A3A3A3A3P96A4").
Definition E_We : axst := ltac2:(tb__ "0|0|
S28S6fS27S1eS21A1S1eS22A1SeP90A1S1eS20A1S1eS24A1SeP91A1A6S4SdS2aS4SdS26S0SdS12S24S22A2S3SdA1A3A3A3P96A4").
Definition E_Wb : axst := ltac2:(tb__ "0|1|
S28S6fS27S1eS21A1S1eS22A1SfZ0A1S1eS20A1S29S1dZ8M0A2SeP91A1A6S4SdS50S4SdS2aS4SdS26S0SdS12S1fS1dSfG0A1A2S22A2S3SdA1A3A3A3A3P96A4").
Definition E_Ee : axst := ltac2:(tb__ "0|1|
S28S6dS27SeP93A1S1eS22A1M0SeP90A1S1aS79S1eS20A1G0A3SeP92A1SeP91A1A6S4SdS26S0SdS12S22S20A2S0SdS10S21S22A2S3SdA1A3A3A3P96A4").
Definition E_Eb : axst := ltac2:(tb__ "0|2|
S28S6dS27SfZ0A1M0S29S1dZ1A2SeP90A1S1fS2bSfN1A1A2M1SeP92A1SeP91A1A6S4SdS4eS4SdS26S0SdS1cS7aG1G0A3S3SdA1A3A3A3P96A4").

Definition cuts_rip : list axst := ltac2:(tb__ "0|0|
S0S60S41S0S60S43S0S60S44S0S60S42S3S60A1A3A3A3A3").
Definition exits_rip : list axst := ltac2:(tb__ "0|0|
S0S60S46S0S60S2fS0S60S39S0S60S30S0S60S3aS0S60S2eS0S60S38S3S60A1A3A3A3A3A3A3A3").
Definition cutpcs_rip : list Z := ltac2:(tb__ "0|0|
S0S5aS6eS0S5aS6fS0S5aS6dS3S5aA1A3A3A3").
Definition FUEL : nat := 400%nat.

Definition vcuts_rip : list vnodeA := ltac2:(tb__ "0|0|
S0S5dS5eS41Z32SfZ0A1A3S0S5dS5eS43Z1eS1dA3S0S5dS5eS44Z14S1dA3S0S5dS5eS42ZaS1fS1dSfZ8A1A2A3S3S5dA1A3A3A3A3").
Definition vexits_rip : list vnodeA := ltac2:(tb__ "0|4|
S0S5dS5eS46Z0SfS69S68Z2Z40A2Z1M0A2A1A3S0S5dS5eS2fZ1fM1S21A3S0S5dS5eS39G1S1fS1dSfG0A1A2A3S0S5dS5eS30Z15M2S24A3S0S5dS5eS3aG2S1fS1dSfZ8A1A2A3S0S5dS5eS2eZbM3S20A3S0S5dS5eS38G3S1fS1dSfZ9A1A2A3S3S5dA1A3A3A3A3A3A3A3").

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
Lemma echeck_rip : ltac2:(tb__ "0|0|
S5bS5S7bS75S45S48S63S57S58A6S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma check_rip : ltac2:(tb__ "0|0|
S5bS5S5fS75S45S48S63S52S53A6S6A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUEL cutpcs_rip NF vcuts_rip vexits_rip cuts_rip exits_rip eq_refl eq_refl echeck_rip). Qed.

Definition s_Pe : wsub := ltac2:(tb__ "0|0|
S78S63S61S2fA1S61S36A1A3").
Definition s_Pb : wsub := ltac2:(tb__ "0|2|
S0S7S59ScA2M0S1S59ScP8eS1fS1dSfZ1M1A1A2A4S0G0S1S59ScP91S29S1dG1A2A4S3G0A1A3A3").
Definition s_We : wsub := ltac2:(tb__ "0|0|
S78S63S61S30A1S61S37A1A3").
Definition s_Wb : wsub := ltac2:(tb__ "0|1|
S0S7S59ScA2M0S1S59ScP8eS1fS1dSfZ8A1A2A4S0G0S1S59ScP90SfZ0A1A4S3G0A1A3A3").
Definition s_Ee : wsub := ltac2:(tb__ "0|0|
S78S63S61S2eA1S61S35A1A3").
Definition s_Eb : wsub := ltac2:(tb__ "0|1|
S0S7S59ScA2M0S1S59ScP8eS1fS1dSfZ1A1A2A4S0G0S1S59ScP8fS1fS2bSfN1A1A2A4S0G0S1S59ScP93SfZ0A1A4S3G0A1A3A3A3").
Lemma ent_Pe : ltac2:(tb__ "0|0|
S5bS5S62S2fS36S33A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Pb : ltac2:(tb__ "0|0|
S5bS5S62S39S36S4bA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_We : ltac2:(tb__ "0|0|
S5bS5S62S30S37S34A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Wb : ltac2:(tb__ "0|0|
S5bS5S62S3aS37S4cA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ee : ltac2:(tb__ "0|0|
S5bS5S62S2eS35S32A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Eb : ltac2:(tb__ "0|0|
S5bS5S62S38S35S4aA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_rip : ltac2:(tb__ "0|0|
S5bS5S8S8S8S8S8S6cS33S63A2S6cS4bS63A2A2S6cS34S63A2A2S6cS4cS63A2A2S6cS32S63A2A2S6cS4aS63A2A2S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma s_Pe_vals : ltac2:(tb__ "0|5|
S5bSbScA1S72S59ScS6bS33A1S0S59P8cM0S0S59P8dM1S0S59P8eS0S59P78M2S0S59P79M3S3S59A1A3A3A3A3A3A4S0ScSeG0A1S0ScSeG1A1S0ScSeG2A1M4S0ScG4S0ScSeG3A1S3ScA1A3A3A3A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma s_We_vals : ltac2:(tb__ "0|5|
S5bSbScA1S72S59ScS6bS34A1S0S59P8cM0S0S59P8dM1S0S59P8eS0S59P78M2S0S59P79M3S3S59A1A3A3A3A3A3A4S0ScSeG0A1M4S0ScSeG1A1S0ScG4S0ScSeG2A1S0ScSeG3A1S3ScA1A3A3A3A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma s_Ee_vals : ltac2:(tb__ "0|4|
S5bSbScA1S72S59ScS6bS32A1S0S59P8dM0S0S59P8eS0S59P8fS0S59P78M1S0S59P79M2S3S59A1A3A3A3A3A3A4S0ScSeG0A1M3S0ScG3S0ScS1aS79S1eS20A1S1eS22A1A3S0ScSeG1A1S0ScSeG2A1S3ScA1A3A3A3A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma s_glob : ltac2:(tb__ "0|1|
S59S7cR1S63A2S5cS5bScS6bS33R2A2SeR2A1M0A3S5cS5bScS6bS34R2A2G0A3S5bScS6bS32R2A2G0A3A2A2F_;Fv;").
Proof.
  intros v Hv. pose proof ids_rip as H. apply andb_prop in H as [H _]. apply andb_prop in H as [H H5].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 _].
  repeat split; apply wsub_get_id with (g := NF); assumption.
Qed.
End Icpt_region.

(* [comment removed for export] *)
Module Drv_printf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "sv"; "mkCell"; "mkObj"; "sobj"; "DUnknown"; "sprop"; "DImage"; "SVar"; "FcsrFrm0"; "mkSS"; "SAlu"; "SPUle"; "valuation"; "SPAlign"; "SPBranch"; "SPNot"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "nat"; "pair"; "true"; "None"; "false"; "list"; "prod"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "NPOST"; "post_regs"; "pre_regs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "opp"; "sub"; "pow"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "fcell"; "bcell"; "FUELP"; "Pre_pf"; "kok"; "vcuts_pf"; "vexits_pf"; "P_pf"; "X_pf"; "facts_pf"; "objs_pf"; "O_file_after"; "O_sbuf_after"; "Posts_pf"; "add"; "ms16"; "regs_pf"; "O_cflag"; "O_file0"; "O_pwin"; "O_realm"; "O_realv"; "O_rtc2"; "O_rtc3w"; "O_sbsh"; "O_sbuf0"; "O_ssp"; "file_cells_after"; "post_regs_pf"; "sbuf_cells_after"; "@Corelib.Init.Logic"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf.PFAddr"; "SBUF"; "FILE"; "PW"; "emit_entry"; "STDIO_WRITE"; "emit_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "ALU_OR"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module PFAddr.
  Definition emit_entry : Z := 0x8c97c.
  Definition emit_ret : Z := 0x8c9c0.
  Definition FMT : Z := 0x14db1.
  Definition FILE : Z := 0xe8fe0.
  Definition SBUF : Z := 0x641988.
  Definition LOWPG : Z := 0x800bc000.
  Definition STDIO_WRITE : Z := 0xd66d8.
  Definition PW : Z := 12288.
End PFAddr.
Import PFAddr.

Definition add (a b : sv) : sv := SAlu ALU_ADD a b.

Definition O_pwin : sobj := ltac2:(tb__ "0|0|
S4S9PaA1S0S2aS50A1A1S0Z0A1S13S1A1S6A5").
Definition fcell (off : Z) (w : Z) (v : Z) : cell := ltac2:(tb__ "0|0|
S3S0S28S4fVoff;A2A1Vw;S0Vv;A1A3").

Definition file_cells_after (n : Z) : list cell := ltac2:(tb__ "0|6|
S12S1S2eZ0M0Z4M1Z5A3S12S1S2eZ28Z8M2S28S4eS2dZ2M3S2bVn;Z1M4A2A2A2A3S12S1S2eZ38G2S4eA3S12S1S2eZ20G2S28S4eZ400A2A3S12S1S2eZ90G1S2bS2cG3Z40A2G4A2M5A3S12S1S2eZ48G2S52A3S12S1S2eZ10G2G0A3S12S1S2eG2G2G0A3S12S1S2eZ88G1G5A3S13S1A1A3A3A3A3A3A3A3A3A3").
Definition O_file_after (n : Z) : sobj := ltac2:(tb__ "0|0|
S4S0Z0A1S0S4fA1S0S28S4fZe8A2A1S49Vn;A1S8A5").
Definition bcell (off : Z) (v : Z) : cell := ltac2:(tb__ "0|0|
S3S0S28S4eVoff;A2A1Z1S0Vv;A1A3").

Definition sbuf_cells_after (n : Z) : list cell := ltac2:(tb__ "0|9|
S14S1aS1A1L_;M0S29Vn;Z1M1A2S12S1S2fZ0Z30M2A2S13S1A1A3M3G0S29Vn;Z2M4A2S12S1S2fG1ZaM5A2G3A3M6G0S29Vn;Z3M7A2S12S1S2fG7G5A2S12S1S2fG4G2A2G6A3A3M8S12S1S2fZ5G5A2S12S1S2fZ4G2A2G8A3A3X14x2X14x2X14x2").
Definition O_sbuf_after (n : Z) : sobj := ltac2:(tb__ "0|0|
S4S0Z0A1S0S4eA1S0S28S4eZ400A2A1S4bVn;A1S6A5").

Definition O_file0 : sobj := ltac2:(tb__ "0|0|
S4S0Z0A1S0S4fA1S0S28S4fZe8A2A1S13S1A1S8A5").
Definition O_sbuf0 : sobj := ltac2:(tb__ "0|0|
S4S0Z0A1S0S4eA1S0S28S4eZ400A2A1S13S1A1S6A5").

Definition O_sbsh : sobj := ltac2:(tb__ "0|3|
S4S0Z0A1M0S0Z800c0330A1M1S0Z800c0340A1S12S1S3G1Z8M2G0A3S12S1S3S0Z800c0338A1G2G0A3S13S1A1A3A3S6A5").

Definition O_rtc3w : sobj := ltac2:(tb__ "0|3|
S4S0Z0A1S0Zeed98A1M0S0Zeed9aA1S12S1S3G0Z1M1S0G1A1M2A3S12S1S3S0Zeed99A1G1G2A3S13S1A1A3A3S6A5").

Definition O_rtc2 : sobj := ltac2:(tb__ "0|3|
S4S0Z0A1M0S0Zeeda0A1M1S0Zeedb8A1S12S1S3G1Z8M2S0Z7fffffffffffA1A3S12S1S3S0Zeeda8A1G2G0A3S12S1S3S0Zeedb0A1G2G0A3S13S1A1A3A3A3S6A5").

Definition O_cflag : sobj := ltac2:(tb__ "0|1|
S4S0Z0A1S0Z17fc38A1M0S0Z17fc40A1S12S1S3G0Z8S0Z100000000A1A3S13S1A1A3S8A5").
Definition O_realv : sobj := ltac2:(tb__ "0|0|
S4S0Z0A1S0Ze6668A1S0Ze6678A1S13S1A1S8A5").
Definition O_realm : sobj := ltac2:(tb__ "0|2|
S4S0Z0A1S0Ze6778A1M0S0Ze6788A1S12S1S3G0Z8M1S0Zdac00A1A3S12S1S3S0Ze6780A1G1S0Zdb004A1A3S13S1A1A3A3S6A5").

Definition O_ssp : sobj := ltac2:(tb__ "0|1|
S4S0Z0A1S0Z6412b8A1M0S0Z6412c0A1S12S1S3G0Z8S9PfA1A3S13S1A1A3S8A5").
Definition objs_pf (ofile osbuf : sobj) : list sobj := ltac2:(tb__ "0|0|
S1cS5S12S5S41S12S5Vofile;S12S5Vosbuf;S12S5S46S12S5S45S12S5S44S12S5S3fS12S5S43S12S5S42S12S5S48S13S5A1A3A3A3A3A3A3A3A3A3A3S21A3").

Definition X_pf : list (sv * sv) := ltac2:(tb__ "0|1|
S12S1bS2S2A2M0S16S2S2S0Z14d80A1S0Z40A1A4S12G0S16S2S2S3cS9PaA1S0S2aS50A1A1A2S0S50A1A4S13G0A1A3A3").

Definition ms16 (d : Z) : sprop := ltac2:(tb__ "0|0|
S11S10S60ScS5eScS5fS0Z28A1S3cS9PaA1S0S2aVd;A1A1A2A3S0ZfA1A3S0Z0A1A3A1").
Definition facts_pf : list sprop := ltac2:(tb__ "0|2|
S12S7SfPaM0Z4A2S12S7SdS0S28S20Z10000A2A1S9G0A1M1A2S12S7SdG1S0S2bS2cZ2Z2fA2Z10A2A1A2S12S7S3dZ958A1S12S7S3dZ928A1S13S7A1A3A3A3A3A3").

Definition regs_pf : list sv := ltac2:(tb__ "0|1|
S24S27S12S1bS15S2A2M0S16S15S2U3S0Z10800A1A4S12G0S16S15S2UbS0Z0A1A4S13G0A1A3A3A2").

Definition Pre_pf0 : axst := ltac2:(tb__ "0|0|
S1fSbS51S3eS23SaS18S2A1S38S40S47A2S37S22S19A9S36A2").

Definition Pre_pf (k : Z) : axst := ltac2:(tb__ "0|0|
S1fSbS51S3eS23SaS18S2A1S38S39Vk;A1S3aVk;A1A2S37S22S19A9S36A2").
Definition post_regs_pf : list sv := ltac2:(tb__ "0|1|
S24S26S22A1S12S1bS15S2A2M0S16S15S2U3S0Z10800A1A4S13G0A1A3A2").
Definition P_pf (k : Z) : axst := ltac2:(tb__ "0|1|
S1fSbS53S4aS23SaS18S2A1S38S39S28Vk;Z1A2M0A1S3aG0A1A2S37S25S19A9S36A2").
Definition Posts_pf (k : Z) : list leafA := ltac2:(tb__ "0|0|
S12S59S5aS35Vk;A1S63A2S13S59A1A3").

Definition FUELP : nat := 8000%nat.
Definition vcuts_pf (k : Z) : list vnodeA := ltac2:(tb__ "0|0|
S12S54S55S31Vk;A1Z1S0Z0A1A3S13S54A1A3").
Definition vexits_pf (k : Z) : list vnodeA := ltac2:(tb__ "0|1|
S12S54S55S35Vk;A1Z0M0S0G0A1A3S13S54A1A3").
Lemma echeck_pf1 : ltac2:(tb__ "0|1|
S4cS14S57S1eS30S13S1dA1S22S33Z1M0A1S34G0A1A6S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma echeck_pf2 : ltac2:(tb__ "0|1|
S4cS14S57S1eS30S13S1dA1S22S33Z2M0A1S34G0A1A6S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma echeck_pf3 : ltac2:(tb__ "0|1|
S4cS14S57S1eS30S13S1dA1S22S33Z3M0A1S34G0A1A6S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition kok (k : Z) : Prop := ltac2:(tb__ "0|0|
S4dS4cS1dVk;Z1A3S4dS4cS1dVk;Z2A3S4cS1dVk;Z3A3A2A2").
Lemma echeck_pf : ltac2:(tb__ "0|0|
S1dS32R1A1S4cS14S57S1eS30S13S1dA1S22S33R2A1S34R2A1A6S17A3F_;Fk;").
Proof. intros k [->|[->| ->]]; [exact echeck_pf1 | exact echeck_pf2 | exact echeck_pf3]. Qed.
Lemma check_pf : ltac2:(tb__ "0|1|
S1dS32R1A1S4cS14S56S1eS30S13S1dA1S22S12S58S31R2A1S13S58A1M0A3S12S58S35R2A1G0A3A6S17A3F_;Fk;").
Proof. intros k Hk. exact (check_cfgA_of_ecfgIA segs FUELP [] NF (vcuts_pf k) (vexits_pf k) [Pre_pf k] [P_pf k] eq_refl eq_refl (echeck_pf k Hk)). Qed.

Section Sum.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ok_frameA segs ok J.
Hypothesis Hst : stableA segs NF J.

Theorem printf_sum : ltac2:(tb__ "0|0|
S1dSeS1aS5dQ40A1A1S32R3A1S62S1eVok;S5cS1eVJ;S31R4A1R3R2A5S5bS1eVJ;S22R3R2S3bR4A1A6A4F_;Ftp;Frho;Fk;").
Proof.
  intros k rho tp Hk.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF (Pre_pf k) rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELP [] NF [Pre_pf k] [P_pf k] (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp (Posts_pf k)) tp HokG HstG (check_pf k Hk)); [|left; reflexivity].
  intros E rhoE [<-|[]]. apply exit_postA. left; reflexivity.
Qed.
End Sum.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.

Theorem printf_sum_ex : ltac2:(tb__ "0|0|
S1dSeS1aS5dQ40A1A1S32R3A1S61S1eS5cS1eVJ;S31R4A1R3R2A5S5bS1eVJ;S22R3R2S3bR4A1A6A3F_;Ftp;Frho;Fk;").
Proof.
  intros k rho tp Hk.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF (Pre_pf k) rho tp w Hw) | intros w Hw; exact Hw |].
  change (Pre_pf k) with (vna_state (mkVNA (Pre_pf k) 1 (SLit 0))).
  apply (cfg_complete_autoIA segs FUELP [] NF (vcuts_pf k) (vexits_pf k) (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp (Posts_pf k)) tp HstG); [ | exact (echeck_pf k Hk) | | left; reflexivity].
  { intros m [<-|[]]. cbv; congruence. }
  intros E rhoE [<-|[]].
  apply (eexit_post_IA0 segs J NF rho (vcuts_pf k) (Posts_pf k) (mkVNA (P_pf k) 0 (SLit 0))). left; reflexivity.
Qed.
End SumEx.
End Drv_printf.

(* [comment removed for export] *)
Module Str_istrlen.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "bool"; "true"; "prod"; "None"; "false"; "list"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SLit"; "valuation"; "holds"; "sobj"; "rw"; "SPUle"; "FcsrFrm0"; "SPBranch"; "agree_below"; "mkSS"; "rl"; "sprop_below"; "ss_facts"; "ss_next"; "DList"; "SPEq"; "SPNot"; "cell"; "eval"; "mkObj"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "two62"; "cut_regs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen"; "cur"; "E_back"; "E_ret"; "inv"; "s_back"; "s_ret"; "Pre_isl"; "add"; "base_facts"; "C_0"; "FirstNul"; "O_str"; "P_isl0"; "isl_state"; "BYTE"; "C"; "FUEL_ISL"; "F_post"; "Posts_isl"; "cutpcs_isl"; "P_isl"; "cuts_isl"; "exits_isl"; "vcuts_isl"; "vexits_isl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "leafA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_sub"; "wsub"; "wsub_id_below"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "lt"; "modulo"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen.ISLAddr"; "isl_loop"; "isl_ret"; "isl_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes"; "nthb"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv HasZero StrBytes CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2 CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ISLAddr.
  Definition isl_entry : Z := 0x6fff0.
  Definition isl_loop : Z := 0x6fff4.
  Definition isl_ret : Z := 0x70008.
End ISLAddr.
Import ISLAddr.

Definition FUEL_ISL : nat := 60%nat.

Definition O_str : sobj := ltac2:(tb__ "0|0|
S21SdPcA1SeZ0A1SdP11A1S1S1fA1S1cP3A1A5").
Definition base_facts : list sprop := ltac2:(tb__ "0|3|
S0ScS15S5dSdP10A1SdP11A1M0A3S0ScS13G0SeS28A1M1A2S0ScS13SeZ1A1SdPcA1M2A2S0ScS13G2G1A2S1ScA1A3A3A3A3").
Definition Pre_isl : axst := ltac2:(tb__ "0|0|
S46S17S60S2bS26S14S7SbA1S0S11S37S1S11A1A3S34S25S8A9S1S6SbSbA2A1A2").

Definition cur : sv := SVar 120.
Definition add (a b : sv) : sv := SAlu ALU_ADD a b.
Definition BYTE (e : sv) : sv := SExt false 8 (SLBytes 3 e 1).
Definition inv : list sprop := ltac2:(tb__ "0|0|
S0ScS13S2cSdP10A1A2S1ScA1A3").
Definition isl_state (pc : Z) (regs : list (nat * sv)) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
S46S17Vpc;S27S29S25A1Vregs;A2S26S14S7SbA1S0S11S37S1S11A1A3SaScVfacts;S34A3Vnx;S8A9S1S6SbSbA2A1A2").

Definition C_0 : axst := ltac2:(tb__ "0|1|
S39S5eS0S6S2SbA2M0S3S2SbUaSdPcA1A4S0G0S3S2SbUbS2cA4S0G0S3S2SbUcSdP79A1A4S1G0A1A3A3A3S1ScA1P87A4").
Definition C : axst := ax_add_facts inv C_0.

Definition E_back : axst := ltac2:(tb__ "0|2|
S39S5eS0S6S2SbA2M0S3S2SbUaSdPcA1A4S0G0S3S2SbUbS33S2cSeZ1A1A2A4S0G0S3S2SbUcS3aS2cA1M1A4S1G0A1A3A3A3S0ScS15S5cG1SeZ0A1A3S2fA3P87A4").
Definition E_ret : axst := ltac2:(tb__ "0|2|
S39S5fS0S6S2SbA2M0S3S2SbUaS2cA4S0G0S3S2SbUbS33S2cSeZ1A1A2A4S0G0S3S2SbUcS3aS2cA1M1A4S1G0A1A3A3A3S0ScS1eS15S5cG1SeZ0A1A3A1S2fA3P87A4").

Definition P_isl0 : axst := ltac2:(tb__ "0|1|
S46S17S5fS27S2aS25A1S0S6S2SbA2M0S3S2SbUaSdP8cA1A4S1G0A1A3A2S26S14S7SbA1S0S11S37S1S11A1A3S34P8dS8A9S1S6SbSbA2A1A2").
Definition F_post : list sprop := ltac2:(tb__ "0|0|
S0ScS1dSdP8cA1SdP10A1A2S1ScA1A3").
Definition P_isl : axst := ax_add_facts F_post P_isl0.
Definition Posts_isl : list leafA := ltac2:(tb__ "0|0|
S0S4aS4bS40S6cA2S1S4aA1A3").

Definition cuts_isl : list axst := ltac2:(tb__ "0|0|
S0S48S32S0S48S3bS1S48A1A3A3").
Definition exits_isl : list axst := ltac2:(tb__ "0|0|
S0S48S2eS0S48S2dS1S48A1A3A3").
Definition cutpcs_isl : list Z := [isl_loop].

Definition vcuts_isl : list vnodeA := ltac2:(tb__ "0|0|
S0S4cS4dS32Z32SeZ0A1A3S0S4cS4dS3bZ1eS2cA3S1S4cA1A3A3").
Definition vexits_isl : list vnodeA := ltac2:(tb__ "0|0|
S0S4cS4dS2eZ0S2cA3S0S4cS4dS2dZ1fS33S2cSeZ1A1A2A3S1S4cA1A3A3").
Lemma echeck_isl : ltac2:(tb__ "0|0|
S22S4S6dS45S3cS3fS25S43S44A6S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_isl : ltac2:(tb__ "0|0|
S22S4S4eS45S3cS3fS25S41S42A6S5A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUEL_ISL cutpcs_isl NF vcuts_isl vexits_isl cuts_isl exits_isl eq_refl eq_refl echeck_isl). Qed.

Definition s_back : wsub := ltac2:(tb__ "0|0|
S61S25S47S2dA1S47S35A1A3").
Definition s_ret : wsub := ltac2:(tb__ "0|0|
S61S25S47S2eA1S47S38A1A3").
Lemma ent_back : ltac2:(tb__ "0|0|
S22S4S49S2dS35S30A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_ret : ltac2:(tb__ "0|0|
S22S4S49S2eS38S31A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_isl : ltac2:(tb__ "0|0|
S23S22S4S53S30S25A2S5A3S22S4S53S31S25A2S5A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma s_vals : ltac2:(tb__ "0|2|
S23S22SbS50S30P78A2S33S2cSeZ1A1A2A3S23S22SbS50S31P8cA2S2cA3S23S22SbS50S30P10M0A2SdG0A1M1A3S22SbS50S31G0A2G1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma inv_below : ltac2:(tb__ "0|0|
S22S4S68ScS19S1bS47S35A1A1A1S2fA3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F_post_below : ltac2:(tb__ "0|0|
S22S4S68ScS19S1bS47S38A1A1A1S3dA3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition FirstNul (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S23S22S54S67S18Vrho;P3A2M0S57Q40S12Vrho;P10A2A2M1A2Z0M2A3S54S23S58G2R1A2S5aR1G1A2A2S24S22S54S67G0R2A2G2A3A1F_;Fi;A2").

Lemma FirstNul_agree : ltac2:(tb__ "0|1|
S55SfSfS6eP10R3A2S16R4R3R2A3S36R4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof.
  intros n rho rho' Hn (A & B & C) [H1 H2]. unfold FirstNul. rewrite <- (A 16%positive Hn), <- B. split; assumption.
Qed.

Lemma two62_mod : ltac2:(tb__ "0|1|
S22S54S5bS28S59Z2M0Z40A2A2S59G0Z3eA2A3"). Proof. reflexivity. Qed.
Lemma rw_sub : ltac2:(tb__ "0|0|
SfS52S55S22S56Q40A1S12S51R3R2A2R1A2S20R3S50R2R1A2A2A3Fi;Fs;Frho;"). Proof. reflexivity. Qed.
Lemma rl_sub : ltac2:(tb__ "0|0|
SfS52S22S55S9S56Q8A1A1F_;S18S51R2R1A2A1S18R2A1A3Fs;Frho;"). Proof. reflexivity. Qed.

Section Glue.
Variable rho0 : valuation.
Hypothesis HFN : FirstNul rho0.

Lemma exit_facts : ltac2:(tb__ "0|3|
SfScS4fScS10R2A1SaScS0ScR1S2fA3S34A3A3S23S10R3R2A2S23S58S57Q40M0S12R3P78A2A2S57G0S12R3P10A2A2M1A2S23S5aG1S57G0S12R3P11A2A2M2A2S58G2S59Z2Z3eA2A2A2A2A2F_;Ff;Frho;").
Proof.
  intros rho f HF. cbn [app inv] in HF.
  apply Forall_cons_iff in HF as [Hf HF]. apply Forall_cons_iff in HF as [Hi HF].
  apply Forall_cons_iff in HF as [Hb1 HF]. apply Forall_cons_iff in HF as [Hb2 _].
  split; [exact Hf|].
  pose proof (urange (rw rho 120)). pose proof (urange (rw rho 16)). pose proof (urange (rw rho 17)).
  cbn [holds eval branch_taken cur] in Hi, Hb1, Hb2. unfold bv_ltu in Hb1.
  rewrite ?lit_unsigned, ?two62_mod in Hb2.
  apply Z.ltb_lt in Hb1. repeat split; lia.
Qed.

Lemma glue_back : ltac2:(tb__ "0|0|
SfS16S25Vrho0;R1A3S4fScS10R2A1S1aS47S2dA1A1A3S4fScS10S51R3S30A2A1S2fA3F_;F_;Frho;").
Proof.
  intros rho Hag HF. pose proof (FirstNul_agree NF rho0 rho ltac:(cbv; reflexivity) Hag HFN) as [FN0 FN1].
  destruct (exit_facts rho _ HF) as (Hb & I1 & I2 & I3). apply holds_BNZ in Hb. change (eval rho cur) with (rw rho 120) in Hb.
  pose proof (urange (rw rho 120)) as R.
  pose proof (fn_step (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) I1 Hb) as ST.
  destruct s_vals as (V1 & _ & V3 & _).
  unfold inv. constructor; [|constructor]. cbn [holds]. unfold cur. cbn [eval]. rewrite !rw_sub, V1, V3. unfold add. cbn [eval].
  rewrite add_val, lit_unsigned. unfold cur. cbn [eval]. change (1 mod 2 ^ 64) with 1. rewrite Z.mod_small by lia. lia.
Qed.

Lemma glue_ret : ltac2:(tb__ "0|0|
SfS16S25Vrho0;R1A3S4fScS10R2A1S1aS47S2eA1A1A3S4fScS10S51R3S31A2A1S3dA3F_;F_;Frho;").
Proof.
  intros rho Hag HF. pose proof (FirstNul_agree NF rho0 rho ltac:(cbv; reflexivity) Hag HFN) as [FN0 FN1].
  destruct (exit_facts rho _ HF) as (Hb & I1 & I2 & I3). apply holds_BZ in Hb. change (eval rho cur) with (rw rho 120) in Hb.
  pose proof (urange (rw rho 120)) as R.
  pose proof (fn_found (rl rho 3) (bv_unsigned (rw rho 16)) FN1 (bv_unsigned (rw rho 120)) ltac:(lia) I1 Hb) as FD.
  destruct s_vals as (_ & V2 & _ & V4).
  unfold F_post. constructor; [|constructor]. cbn [holds eval]. rewrite !rw_sub, V2, V4. unfold cur. cbn [eval]. apply bv_eq. exact FD.
Qed.
End Glue.

Theorem istrlen_sum : ltac2:(tb__ "0|0|
S6bOF_;S64SfS9S56Q40A1A1S66S45R4R3A3S65S45S25R4A3S36R4A1S6aS45R7S63S45R6S32R5R4A5S62S45R6S25R5R4S3eA6A4F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HFN. destruct ids_isl as [I1 I2].
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_isl rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_ISL cutpcs_isl NF cuts_isl exits_isl (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_isl) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - exact HstG.
  - exact check_isl.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply (exit_post_GA segs ok J NF rho cuts_isl Posts_isl E_ret P_isl0 F_post s_ret tp);
        [left; reflexivity | exact ent_ret | exact I2 | exact Hst | exact F_post_below | intros r Hag HF; exact (glue_ret rho HFN r Hag HF)].
    + apply (exit_reenterA segs ok _ NF cuts_isl _ E_back C_0 inv s_back tp);
        [right; left; reflexivity | exact ent_back | exact I1 | exact HstG | exact inv_below
        | intros r tp' tr md [Hag _] HF; exact (glue_back rho HFN r Hag HF)].
  - left; reflexivity.
Qed.

Theorem istrlen_sum_ex : ltac2:(tb__ "0|0|
S64SfS9S56Q40A1A1S65S45S25R3A3S36R3A1S69S45S63S45R5S32R4R3A5S62S45R5S25R4R3S3eA6A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HFN. destruct ids_isl as [I1 I2].
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_isl rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_isl with (vna_state (mkVNA Pre_isl 50 (SLit 0))).
  apply (cfg_complete_autoIA segs FUEL_ISL cutpcs_isl NF vcuts_isl vexits_isl (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_isl) tp).
  - exact HstG.
  - intros n Hin. unfold vcuts_isl in Hin. repeat (destruct Hin as [<-|Hin]; [cbv; congruence|]). destruct Hin.
  - exact echeck_isl.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[]]].
    + apply (eexit_post_IA segs J NF rho vcuts_isl Posts_isl (mkVNA E_ret 0 cur) P_isl0 F_post s_ret tp);
        [left; reflexivity | exact ent_ret | exact I2 | exact Hst | exact F_post_below | intros r Hag HF; exact (glue_ret rho HFN r Hag HF)].
    + apply (eexit_reenter_IA segs _ NF vcuts_isl _ (mkVNA E_back 31 (add cur (SLit 1))) (mkVNA C 30 cur) inv C_0 s_back tp);
        [right; left; reflexivity | reflexivity | exact ent_back | exact I1 | exact HstG | exact inv_below
        | intros r tp' tr md [Hag _] HF; split; [exact (glue_back rho HFN r Hag HF) | right; split; [| cbn; lia]]
        | cbn; lia | cbn; lia].
      destruct s_vals as (V1 & _). cbn [vna_var]. unfold cur at 2. cbn [eval]. rewrite rw_sub, V1. lia.
  - left; reflexivity.
Qed.
End Str_istrlen.

(* [comment removed for export] *)
Module Str_memcpyAH.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "None"; "false"; "list"; "prod"; "true"; "app"; "bool"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sprop"; "SLit"; "sv"; "sobj"; "sstate"; "SPBranch"; "FcsrFrm0"; "SAlu"; "cell"; "mkSS"; "SPUle"; "holds"; "valuation"; "DUnknown"; "SPAlign"; "mkObj"; "mkCell"; "SExt"; "SPNot"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "NPOST"; "post_regs"; "pre_regs"; "cut_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "mkVN"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "ALU_ADD"; "ALU_AND"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memcpyAH.States"; "F_ah"; "N14a"; "O_srcH"; "O_dst0"; "P_ah1"; "P_ah2"; "C0_ah"; "C1_ah"; "HV"; "O_dstH"; "Pre_ah"; "Z_ah1"; "Z_ah2"; "B120a"; "B121a"; "F_c1a"; "F_z"; "Fge16"; "J120a"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "memcpy_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memcpyAH"; "FUELAH"; "cutpcs_ah"; "Posts_ahA"; "Pre_ahA"; "cuts_ahA"; "Z_ah"; "exits_ahA"; "vcuts_ahA"; "vexits_ahA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "@Corelib.Init.Logic"; "False"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section States.
Variable base : Z.

Definition HV : positive := 16%positive.
Definition N14a : sprop := SPUle (SVar 14) (SLit two62).

Definition F_ah : list sprop := ltac2:(tb__ "0|1|
S0SdS1bPcZ2M0A2S0SdS1bPdG0A2S0SdS17SeZ4A1ScPeA1A2S1SdA1A3A3A3").
Definition O_dst0 : sobj := ltac2:(tb__ "0|0|
S1cScPcA1SeZ0A1ScPeA1S1S15A1S1aA5").
Definition O_dstH : sobj := ltac2:(tb__ "0|1|
S1cScPcA1SeZ0A1M0ScPeA1S0S15S1dG0Z4S1eS8Q20ScS37A1A3A3S1S15A1A3S1aA5").
Definition O_srcH : sobj := ltac2:(tb__ "0|1|
S1cScPdA1SeZ0A1M0ScPeA1S0S15S1dG0Z4ScS37A1A3S1S15A1A3S1aA5").

Definition Pre_ah : sstate := ltac2:(tb__ "0|0|
S16Vbase;S27S23S13S4SfA1S0S10S32S0S10S31S1S10A1A3A3S0SdS30S2fA3S22S5A9").

Definition Fge16 : sprop := ltac2:(tb__ "0|0|
S1fS12S2bScPeA1SeZ10A1A3A1").
Definition C0_ah : sstate := ltac2:(tb__ "0|1|
S16S42Vbase;Z12cA2S24S27S0S7S2SfA2M0S3S2SfUdScPcA1A4S0G0S3S2SfUeSeZfA1A4S0G0S3S2SfUfSeZ0A1A4S1G0A1A3A3A3A2S23S13S4SfA1S0S10S32S0S10S31S1S10A1A3A3S0SdS40S0SdS30S2fA3A3S22S5A9").

Definition J120a : sprop := ltac2:(tb__ "0|0|
S17S14S2cScP78A1ScP79A1A3ScPeA1A2").
Definition B120a : sprop := SPUle (SVar 120) (SLit two62).
Definition B121a : sprop := SPUle (SVar 121) (SLit two62).
Definition F_c1a : list sprop := ltac2:(tb__ "0|1|
S0SdS12S2bSeZfA1ScP79A1A3S0SdS1bP78M0Z4A2S0SdS17SeZ10A1ScG0A1A2S0SdS41S0SdS3cS0SdS3dS1SdA1A3A3A3A3A3A3").
Definition C1_ah : sstate := ltac2:(tb__ "0|3|
S16S42Vbase;Z12cA2S24S28S22A1S0S7S2SfA2M0S3S2SfUaScPcA1M1A4S0G0S3S2SfUbS14S2cScPdA1ScP78A1M2A3A4S0G0S3S2SfUcScP79A1A4S0G0S3S2SfUdS14S2cG1G2A3A4S0G0S3S2SfUeSeZfA1A4S1G0A1A3A3A3A3A3A2S23S13S4SfA1S0S10S38S0S10S31S1S10A1A3A3S9SdS3eS0SdS30S2fA3A3P87S5A9").

Definition P_ah (off : Z) : sstate := ltac2:(tb__ "0|1|
S16S42Vbase;Voff;A2S24S26S22A1S0S7S2SfA2M0S3S2SfUaScPcA1A4S1G0A1A3A2S23S13S4SfA1S0S10S38S0S10S31S1S10A1A3A3S0SdS30S2fA3S25S5A9").
Definition P_ah1 : sstate := P_ah 0x3d0.
Definition P_ah2 : sstate := P_ah 0x400.
Definition Posts_ah : list leaf := ltac2:(tb__ "0|0|
S0S4dS4fS33S4eA2S0S4dS4fS34S4eA2S1S4dA1A3A3").

Definition F_z : list sprop := ltac2:(tb__ "0|1|
S0SdS12S2bScPeA1M0SeZ10A1A3S0SdS12S2bG0SeZ8A1A3S0SdS12S2eS14S2dG0SeZ4A1A3SeZ0A1A3S1SdA1A3A3A3").
Definition Z_ah (off : Z) : sstate := ltac2:(tb__ "0|1|
S16S42Vbase;Voff;A2S24S26S22A1S0S7S2SfA2M0S3S2SfUaScPcA1A4S1G0A1A3A2S23S13S4SfA1S0S10S32S0S10S31S1S10A1A3A3S9SdS3fS0SdS30S2fA3A3S25S5A9").
Definition Z_ah1 : sstate := Z_ah 0x3d0.
Definition Z_ah2 : sstate := Z_ah 0x400.

Definition cuts_ah : list sstate := ltac2:(tb__ "0|0|
S0S11S39S0S11S35S0S11S36S1S11A1A3A3A3").
Definition exits_ah : list sstate := ltac2:(tb__ "0|0|
S0S11S33S0S11S34S0S11S3aS0S11S3bS1S11A1A3A3A3A3").
Definition cutpcs_ah : list Z := [base + 0x12c].

Definition vcuts_ah : list vnode := ltac2:(tb__ "0|1|
S0S29S2aS39ZaSeZ0A1M0A3S0S29S2aS35Z9G0A3S0S29S2aS36Z7ScP79A1A3S1S29A1A3A3A3").
Definition vexits_ah : list vnode := ltac2:(tb__ "0|2|
S0S29S2aS33Z0M0SeG0A1M1A3S0S29S2aS34G0G1A3S0S29S2aS3aG0G1A3S0S29S2aS3bG0G1A3S1S29A1A3A3A3A3").
End States.

Definition FUELAH : nat := 400%nat.

Lemma ah_junk_absurd : ltac2:(tb__ "0|2|
S19S18R1S17SeZ4A1M0ScPeA1M1A2A2S18R2S12S2bG1SeZ8A1A3A2S18R3S12S2eS14S2dG1G0A3SeZ0A1A3A2S50F_;F_;F_;Frho;").
Proof.
  intros rho H1 H2 H3. cbn [holds eval branch_taken] in H1, H2, H3.
  rewrite lit_unsigned in H1. change (4 mod 2 ^ 64) with 4 in H1.
  unfold bv_ltu in H2. rewrite lit_unsigned in H2. change (8 mod 2 ^ 64) with 8 in H2. apply Z.ltb_lt in H2.
  apply (proj1 (Fs.bv_eqb_eq _ _)) in H3. apply (f_equal bv_unsigned) in H3.
  unfold alu64, alu in H3. rewrite bv_and_unsigned, !lit_unsigned in H3.
  change (4 mod 2 ^ 64) with 4 in H3. change (0 mod 2 ^ 64) with 0 in H3.
  set (n := bv_unsigned (rw rho 14)) in *.
  assert (E : n = 4 \/ n = 5 \/ n = 6 \/ n = 7) by lia.
  destruct E as [E|[E|[E|E]]]; rewrite E in H3; cbv in H3; discriminate.
Qed.

Lemma Z_ah_facts : ltac2:(tb__ "0|0|
S52S52S19S59SdS18R1A1S20S49R3R2A2A1A3S50F_;Frho;Foff;Fbase;").
Proof.
  intros base off rho HF. cbn [Z_ah ss_facts F_z N14a F_ah app] in HF.
  pose proof (Forall_inv (Forall_inv_tail HF)) as H2.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF))) as H3.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF))))))) as H1.
  exact (ah_junk_absurd rho H1 H2 H3).
Qed.

Definition Pre_ahA : axst := liftA (Pre_ah memcpy_entryA).
Definition Posts_ahA : list leafA := map liftLA (Posts_ah memcpy_entryA).
Definition cuts_ahA : list axst := map liftA (cuts_ah memcpy_entryA).
Definition exits_ahA : list axst := map liftA (exits_ah memcpy_entryA).
Definition vcuts_ahA : list vnodeA := map liftVA (vcuts_ah memcpy_entryA).
Definition vexits_ahA : list vnodeA := map liftVA (vexits_ah memcpy_entryA).

Definition check_ahA__runs : ltac2:(tb__ "0|0|
S6SbS6S60A1A1A1") := ltac2:(tb__ "0|0|
S5fS21S44S45S43A1S48A4").
Lemma check_ahA : ltac2:(tb__ "0|0|
S51SaS5dS21S44S45S43A1S22S48S4aA6S8A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUELAH (cutpcs_ah memcpy_entryA) NF cuts_ahA exits_ahA check_ahA__runs); [unfold check_ahA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Lemma echeck_ahA : ltac2:(tb__ "0|0|
S51SaS5eS21S44S45S43A1S22S4bS4cA6S8A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUELAH (cutpcs_ah memcpy_entryA) NF vcuts_ahA vexits_ahA check_ahA__runs); [unfold check_ahA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem memcpy_ah_sumA : ltac2:(tb__ "0|0|
S5cOF_;S55S19S6S58Q40A1A1S57S21R4R3A3S56S21S22R4A3S5bS21R6S54S21R5S47R4R3A5S53S21R5S22R4R3S46A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_ahA rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELAH (cutpcs_ah memcpy_entryA) NF cuts_ahA exits_ahA (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_ahA) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_ahA.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
    + apply exit_postA. in_nth 0.
    + apply exit_postA. in_nth 1.
    + apply triple_factsA. intros HF. exfalso. exact (Z_ah_facts _ _ _ HF).
    + apply triple_factsA. intros HF. exfalso. exact (Z_ah_facts _ _ _ HF).
  - left; reflexivity.
Qed.

Theorem memcpy_ah_sumA_ex : ltac2:(tb__ "0|0|
S55S19S6S58Q40A1A1S56S21S22R3A3S5aS21S54S21R4S47R3R2A5S53S21R4S22R3R2S46A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_ahA rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_ahA with (vna_state (liftVA (mkVN (Pre_ah memcpy_entryA) 10 (SLit 0)))).
  apply (cfg_complete_autoA segs FUELAH (cutpcs_ah memcpy_entryA) NF vcuts_ahA vexits_ahA (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_ahA) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. unfold vcuts_ahA, vcuts_ah in Hin. cbn [map] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbv; congruence|]). destruct Hin.
  - exact echeck_ahA.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
    + apply (eexit_postA segs J NF rho vcuts_ahA Posts_ahA (liftVA (mkVN (P_ah1 memcpy_entryA) 0 (SLit 0)))). in_nth 0.
    + apply (eexit_postA segs J NF rho vcuts_ahA Posts_ahA (liftVA (mkVN (P_ah2 memcpy_entryA) 0 (SLit 0)))). in_nth 1.
    + cbn [vna_state liftVA vn_state]. apply etriple_factsA. intros HF. exfalso. exact (Z_ah_facts _ _ _ HF).
    + cbn [vna_state liftVA vn_state]. apply etriple_factsA. intros HF. exfalso. exact (Z_ah_facts _ _ _ HF).
  - left; reflexivity.
Qed.
End Str_memcpyAH.

(* [comment removed for export] *)
Module Str_memset.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "memset_entryA"; "Posts_memsetA"; "Pre_memsetA"; "cuts_memsetA"; "exits_memsetA"; "vcuts_memsetA"; "vexits_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "option"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "FUEL_MS"; "cutpcs_memset"; "C_164_0"; "C_loop_0"; "E_164"; "E_in"; "s164"; "s_in"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "entailsA"; "axst"; "leafA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition memset_entryA : Z := 0xdb004.

Definition Pre_memsetA : axst := liftA (Pre_memset memset_entryA).
Definition Posts_memsetA : list leafA := map liftLA (Posts_memset memset_entryA).
Definition cuts_memsetA : list axst := map liftA (cuts_memset memset_entryA).
Definition exits_memsetA : list axst := map liftA (exits_memset memset_entryA).
Definition vcuts_memsetA : list vnodeA := map liftVA (vcuts_memset memset_entryA).
Definition vexits_memsetA : list vnodeA := map liftVA (vexits_memset memset_entryA).

Definition check_memsetA__runs : ltac2:(tb__ "0|0|
SaSdSaS21A1A1A1") := ltac2:(tb__ "0|0|
S2aS0SfS10S1A1S4A4").
Lemma check_memsetA : ltac2:(tb__ "0|0|
SeSbS28S0SfS10S1A1S9S4S5A6ScA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUEL_MS (cutpcs_memset memset_entryA) NF cuts_memsetA exits_memsetA check_memsetA__runs); [unfold check_memsetA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Lemma echeck_memsetA : ltac2:(tb__ "0|0|
SeSbS29S0SfS10S1A1S9S6S7A6ScA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUEL_MS (cutpcs_memset memset_entryA) NF vcuts_memsetA vexits_memsetA check_memsetA__runs); [unfold check_memsetA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Lemma ent_164A : ltac2:(tb__ "0|0|
SeSbS1fS8S13S1A1A1S8S11S1A1A1S15S1A1A3ScA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_inA : ltac2:(tb__ "0|0|
SeSbS1fS8S14S1A1A1S8S12S1A1A1S16S1A1A3ScA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma liftA_add_facts : ltac2:(tb__ "0|0|
SaS18A1S19SeS20S8S26R2R1A2A1S27R2S8R1A1A2A3FS;FF;").
Proof. intros F S. reflexivity. Qed.

Theorem memset_sumA : ltac2:(tb__ "0|0|
S25OF_;S1cS17SaS22Q40A1A1S1eS0R4R3A3S1dS0S9R4A3S24S0R6S1bS0R5S3R4R3A5S1aS0R5S9R4R3S2A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_memsetA rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_MS (cutpcs_memset memset_entryA) NF cuts_memsetA exits_memsetA (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_memsetA) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - exact HstG.
  - exact check_memsetA.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[]]]].
    + apply exit_postA. in_nth 0.
    +
      unfold liftA at 1. change (mkA (E_164 memset_entryA) []) with (liftA (E_164 memset_entryA)).
      apply (exit_reenterA segs ok _ NF cuts_memsetA _ (liftA (E_164 memset_entryA)) (liftA (C_164_0 memset_entryA)) F164_sem (s164 memset_entryA) tp).
      * rewrite <- liftA_add_facts. in_nth 1.
      * exact ent_164A.
      * apply s164_id.
      * exact HstG.
      * apply F164_below.
      * intros r tp' tr md _ HF. exact (glue_164 memset_entryA r HF).
    +
      unfold liftA at 1. change (mkA (E_in memset_entryA) []) with (liftA (E_in memset_entryA)).
      apply (exit_reenterA segs ok _ NF cuts_memsetA _ (liftA (E_in memset_entryA)) (liftA (C_loop_0 memset_entryA)) Floop_sem (s_in memset_entryA) tp).
      * rewrite <- liftA_add_facts. in_nth 2.
      * exact ent_inA.
      * apply s_in_id.
      * exact HstG.
      * apply Floop_below.
      * intros r tp' tr md _ HF. exact (glue_in memset_entryA r HF).
  - left; reflexivity.
Qed.

Theorem memset_sumA_ex : ltac2:(tb__ "0|0|
S1cS17SaS22Q40A1A1S1dS0S9R3A3S23S0S1bS0R4S3R3R2A5S1aS0R4S9R3R2S2A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_memsetA rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_memsetA with (vna_state (liftVA (mkVN (Pre_memset memset_entryA) 6 (SLit 0)))).
  apply (cfg_complete_autoA segs FUEL_MS (cutpcs_memset memset_entryA) NF vcuts_memsetA vexits_memsetA (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_memsetA) tp).
  - exact HstG.
  - intros n Hin. unfold vcuts_memsetA, vcuts_memset in Hin. cbn [map] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbv; congruence|]). destruct Hin.
  - exact echeck_memsetA.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[]]]].
    + apply (eexit_postA segs J NF rho vcuts_memsetA Posts_memsetA (liftVA (mkVN (P_ret_memset memset_entryA) 0 (SLit 0)))). in_nth 0.
    + apply (eexit_reenterA segs _ NF vcuts_memsetA _ (liftVA (mkVN (E_164 memset_entryA) 5 (SLit 0))) (liftVA (mkVN (C_164 memset_entryA) 4 (SLit 0)))
               F164_sem (liftA (C_164_0 memset_entryA)) (s164 memset_entryA) tp);
        [in_nth 1 | reflexivity | exact ent_164A | apply s164_id | exact HstG | apply F164_below
        | intros r tp' tr md _ HF; exact (glue_164 memset_entryA r HF) | cbn; lia | cbn; lia].
    + apply (eexit_reenterA segs _ NF vcuts_memsetA _ (liftVA (mkVN (E_in memset_entryA) 3 (SLit 0))) (liftVA (mkVN (C_loop memset_entryA) 2 (SVar 121)))
               Floop_sem (liftA (C_loop_0 memset_entryA)) (s_in memset_entryA) tp);
        [in_nth 2 | reflexivity | exact ent_inA | apply s_in_id | exact HstG | apply Floop_below
        | intros r tp' tr md _ HF; exact (glue_in memset_entryA r HF) | cbn; lia | cbn; lia].
  - left; reflexivity.
Qed.
End Str_memset.

