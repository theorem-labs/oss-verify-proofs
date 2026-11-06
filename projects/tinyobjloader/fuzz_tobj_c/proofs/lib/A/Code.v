(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "sprop"; "SPUle"; "sobj"; "DImage"; "SAlu"; "SVar"; "mkCell"; "mkObj"; "ss_pc"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "option"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "la_state"; "ax_S"; "la_reason"; "mkAX"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "RTC_LO"; "GOT_HI"; "GOT_LO"; "O_got"; "O_rtc"; "RTC_HI"; "SHB"; "g8x"; "segs"; "shb"; "@Corelib.Lists.ListDef"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@Stdlib.Lists.List"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "pow"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition segs : list Segment := Asan.M.loaded_segments.

Definition SHB : Z := 0x7fff8000.
Definition shb : sv := SLit SHB.

Definition ACEIL : Z := 0x7fff7f800000.

Definition GOT_LO : Z := 0xe7bd8.
Definition GOT_HI : Z := 0xe8978.
Definition O_got : sobj := ltac2:(tb__ "0|0|
S9S0Z0A1S0S1aA1S0S19A1ScS1A1S5A5").

Definition RTC_LO : Z := 0xf13f8.
Definition RTC_HI : Z := 0xf1404.

Definition O_rtc : sobj := ltac2:(tb__ "0|2|
S9S0Z0A1S0S18A1M0S0S1dA1SbS1S8G0Z8M1S0S1eA1A3SbS1S8S0S28S18G1A2A1Z4S0Z1A1A3ScS1A1A3A3S5A5").
Definition A_globals : list sobj := ltac2:(tb__ "0|0|
SbS4S1bSbS4S1cScS4A1A3A3").

Definition g8x (g : positive) : sv := ltac2:(tb__ "0|0|
S6S25S7Vg;A1S0Z3A1A3").
Definition F8x (g : positive) (e : sv) : list sprop := ltac2:(tb__ "0|1|
SbS2S3S1fVg;A1M0Ve;A2SbS2S3Ve;S6S24G0S0Z7A1A3A2SbS2S3S7Vg;A1S0S2bS2aZ2Z3dA2Z1A2A1A2ScS2A1A3A3A3").

Definition mkA (S : sstate) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S16VS;VX;S21A3").

Definition show_leafA (L : leafA) : Z * stop_reason := ltac2:(tb__ "0|0|
SfS23S26SaS14S13VL;A1A1A1S15VL;A1A4").
Definition leavesA_at (fuel : nat) (cuts : list Z) (A : axst) (pc : Z) : list axst := ltac2:(tb__ "0|1|
SeSdS11A1M0A1SdS12A1Lx;S17S20Vfuel;Vcuts;VA;S10A5G0S22S11S12S13S27S11S11S29SaS14S13R1A1A1A1Vpc;A2LL;R1A3A4Lls;ScS12A1Xex2").
