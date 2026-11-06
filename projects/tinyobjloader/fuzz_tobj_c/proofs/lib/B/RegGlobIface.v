(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "nil"; "bool"; "true"; "None"; "app"; "false"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "cell"; "sobj"; "mkCell"; "mkObj"; "DUnknown"; "SVar"; "sprop"; "DImage"; "DZero"; "SPAlign"; "FcsrFrm0"; "mkSS"; "swf"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface"; "addk"; "O_flg"; "O_real"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface"; "vB1"; "vS0"; "D_G"; "FRAME_G"; "O_afl1"; "O_afl2"; "O_aglob"; "O_b1"; "O_gl"; "O_gstk"; "O_lla"; "O_llmin"; "O_pgA"; "O_pgB"; "O_ph"; "Pre_G"; "Pre_G_S"; "facts_G"; "fregs_G"; "objs_G"; "regglob_entry"; "regs_G"; "saved_cells"; "vRA"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "pow"; "mul"; "of_nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "O_got"; "O_rtc"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axwf"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition regglob_entry : Z := 0x4a180.
Definition regglob_ret : Z := 0x4aa20.
Definition FRAME_G : Z := 4336.
Definition D_G : Z := 4432.

Definition vB1 : sv := SVar 1.
Definition vS0 : sv := SVar 2.
Definition vRA : sv := SVar 3.

Definition saved_cells : list cell := ltac2:(tb__ "0|1|
S37S0SbS0SdS9S3dN10S3bZ8M0S3cR1A1A2A2A1G0S10S34S18U4R1A2A1A1A3Lk;S38U0UcA2A4").
Definition O_gstk : sobj := ltac2:(tb__ "0|1|
SeS1dS9S39S1eA1A1S9Z0A1S6SbS1SbSdS9N10e0A1Z8M0S9Z1800A1A3S1SbSdS9N10b0A1G0S9Z60A1A3S1SbSdS9N8A1G0S33A3S2SbA1A3A3A3S32A3SfA5").
Definition O_pgA : sobj := ltac2:(tb__ "0|0|
SeS9Z7fffc000A1S9Z0A1S9Z1000A1S2SbA1S13A5").
Definition O_pgB : sobj := ltac2:(tb__ "0|0|
SeS9Z80015000A1S9Z0A1S9Z1000A1S2SbA1S13A5").
Definition O_b1 : sobj := ltac2:(tb__ "0|0|
SeS1cS9Z0A1S9Z10000A1S2SbA1SfA5").

Definition O_lla : sobj := ltac2:(tb__ "0|2|
SeS9Z0A1S9Z170308A1M0S9Z170318A1S1SbSdG0Z8M1S19S1cZ10000A2A3S1SbSdS9Z170310A1G1S19S1cZ4dc0A2A3S2SbA1A3A3SfA5").
Definition O_gl : sobj := ltac2:(tb__ "0|2|
SeS9Z0A1M0S9Zeb930A1S9Zeb980A1S1SbSdS9Zeb938A1Z8M1G0A3S1SbSdS9Zeb970A1G1S9S3aZ2Z3cA2A1A3S2SbA1A3A3SfA5").

Definition O_afl1 : sobj := ltac2:(tb__ "0|0|
SeS9Z0A1S9Zeb8b8A1S9Zeb8e4A1S1SbSdS9Zeb8d0A1Z4S9Z1A1A3S2SbA1A3SfA5").
Definition O_afl2 : sobj := ltac2:(tb__ "0|1|
SeS9Z0A1S9Zeb8f0A1S9Zeb930A1S1SbSdS9Zeb90dA1Z1M0S9G0A1A3S1SbSdS9Zeb91cA1Z4S9Z2A1A3S2SbA1A3A3SfA5").
Definition O_aglob : sobj := ltac2:(tb__ "0|0|
SeS9Z0A1S9Ze91f0A1S9Zea9f0A1S2SbA1S12A5").

Definition O_llmin : sobj := ltac2:(tb__ "0|0|
SeS9Z0A1S9Ze67c0A1S9Ze67c8A1S2SbA1S12A5").
Definition O_ph : sobj := ltac2:(tb__ "0|2|
SeS9Z0A1S9Zed91cA1M0S9Zed91dA1S1SbSdG0Z1M1S9G1A1A3S2SbA1A3SfA5").

Definition objs_G : list sobj := ltac2:(tb__ "0|0|
S1ScS25S1ScS28S1ScS29S1ScS23S1ScS26S1ScS24S1ScS20S1ScS21S1ScS22S1ScS27S1ScS2aS1ScS1aS1ScS1bS1ScS3eS1ScS3fS2ScA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition facts_G : list sprop := ltac2:(tb__ "0|0|
S1S11S14P2Z4A2S1S11S14P1ZcA2S2S11A1A3A3").

Definition reg_G (r : nat) : sv := ltac2:(tb__ "0|1|
S0SaLr;Vr;S9Z0A1S0S0SaLn;R1S10S34S18U3cVr;A2A1A1M0S0S0SaLn0;R1S19S1dS39S1fA1A2S0S0SaLn1;R1S9Z10800A1S0S0SaLn2;R1S9Z621278A1S0S0SaLn3;R1G0S0S0SaLn4;R1G0S0S0SaLn5;R1G0S0S0SaLn6;R1S1dS0S0SaLn7;R1S9Ze91f0A1S0S0SaLn8;R1G0S0S0SaLn9;R1G0S0S0SaLn10;R1G0S0S0SaLn11;R1G0S0S0SaLn12;R1G0S0S0SaLn13;R1G0S0S0SaLn14;R1G0S0S0SaLn15;R1G0S0S0SaLn16;R1G0S0S0SaLn17;R1S9S3aZ2Z3cA2A1S0S0SaLn18;R1G0S0S0SaLn19;R1G0S0S0SaLn20;R1G0S0S0SaLn21;R1G0S0S0SaLn22;R1S9Zeb8b8A1S0S0SaLn23;R1S9Zeb930A1S0S0SaLn24;R1S9Zeb970A1S0G0Ln25;X0x2Ln24;X0x2Ln23;X0x2Ln22;X0x2Ln21;X0x2Ln20;X0x2Ln19;X0x2Ln18;X0x2Ln17;X0x2Ln16;X0x2Ln15;X0x2Ln14;X0x2Ln13;X0x2Ln12;X0x2Ln11;X0x2Ln10;X0x2Ln9;X0x2Ln8;X0x2Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition regs_G : list sv := map reg_G (seq 0 32).
Definition fregs_G : list sv := ltac2:(tb__ "0|0|
S37S0SaS0S10S34S18U14R1A2A1A1Lr;S38U0U20A2A4").

Definition axG (S : sstate) : axst := ltac2:(tb__ "0|0|
S42VS;S2S8SaSaA2A1S9S40A1A3").
Definition Pre_G_S : sstate := ltac2:(tb__ "0|0|
S16S30S31S2eS15S5SaA1S2fS2dS43S7A9").
Definition Pre_G : axst := axG Pre_G_S.

Lemma Pre_G_wf : ltac2:(tb__ "0|0|
S36S35S3S17S2cA1S4A3S35S3S41S2bA1S4A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
