(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatPopulate4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5cell"; "5wr"; "6msteps"; "7getr"; "7mkst"; "7regupd"; "8loaded_segments"; "9add"]; ["9le"; "9lt"; "9mul"; "9pow"; "9sub"; "0a0v"; "0chp"; "0fa"; "0fx"; "0ia"; "0n"; "0nf"; "0nf2"; "0r"; "0regs"; "0rom"]; [":BV"; ":Z_to_bv"; ":bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".
Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_gfa_popa_fn : ltac2:(TCodec.tc2 tcn__JatPopulate4 "TL&5y5'Q2yR0%211%5241'0y8%611%311p061'4'3&;r9(Q0+8(1%33A21%6251&Q1r5%22C1%;3C41r:+9%;3I19%>231r7%92J1%B3J31r;+:%B3Q01@%E231r3%@2Q11%I3Q131r<+=%I3Q71G%L231%N3Q61=r=+>%N3Q<1L%Q1231%Q33Q;1B&@z%221J&A&?+T0%22G1&C+2+R0%3221%8251'2%=2<Q?%;2Q@Q6%3221+Q0%:291%?2Q31r?%D2C1%B22;%:221r>%H2G1%F22?%>221%K2JQ5%I2Q6B%A221&8&>rDrA+@%O221u8%756521>':&<vHrF+ZkVL%R<3RH1R:/01RHrE%756521>&=+1%RB3S01R@+Zkb8%RD3S01RB/01S0%63<41rC%RC2S41%933R71rB%RF2S71%<33R31&Dr@%221Q;%RK2S<1%A35R31+?%S33SA1S1%RO2S@Q@%E3421+B%S73SE1S5%S32SDQ@%I3421+E%S;3SI1S9%S72SHQ:%M3421+F%S?3SM1S=%S;2SLB%Q13421+ZkdD%SC3SO1SA/01SO%Q=5Q<41Q7QD%Q?3QFQ71p0QA1p0QJ1p0QN1p0R31p0R81p0R<1p0RA1p0RK1p0RO1p0S51p0S;1p0SC1p0SK1pQ<T81pQHT91pQFT:1pQ>T;1pQLT<1pQDT=1pR0T?1p>T@1pQNTF1").
Proof.
intros regs M rom ia r chp n nf a0v H8 H9 H10 H13 H14 Hr Hr' Hnf Hn Hia Hchp Ha0 Cnf.
zld (ltac:(oF' 0x56cdc%Z)) (ltac:(oD' 0x56cdc%Z)) (r + 16) Cnf.
zbtk (ltac:(oF' 0x56ce0%Z)) (ltac:(oD' 0x56ce0%Z)).
zstep (ltac:(oF' 0x56e2c%Z)) (ltac:(oD' 0x56e2c%Z)). zstep (ltac:(oF' 0x56e30%Z)) (ltac:(oD' 0x56e30%Z)). zstep (ltac:(oF' 0x56e34%Z)) (ltac:(oD' 0x56e34%Z)). zstep (ltac:(oF' 0x56e38%Z)) (ltac:(oD' 0x56e38%Z)). zstep (ltac:(oF' 0x56e3c%Z)) (ltac:(oD' 0x56e3c%Z)). zstep (ltac:(oF' 0x56e40%Z)) (ltac:(oD' 0x56e40%Z)).
stepn (ltac:(oF' 0x56e44%Z)) (ltac:(oD' 0x56e44%Z)).
zret.
Qed.
#[using="Type"] Lemma art_gfa_popb_fn : ltac2:(TCodec.tc2 tcn__JatPopulate4 "U>&5y5'Q2yR0%211%5241'0y8%611%311p061'4'3&;r9(Q0+:(1%33A21%6251&Q1+1%22C1%;3C41r:+8%;3I19%>231r7%92J1%B3J31r;+B%B3Q01@%E231r3%@2Q11%I3Q131r<+D%I3Q71G%L231r8%G2Q81%Q03Q831r=+E%Q03Q>1N%Q3231%Q53Q=16r>+F%Q53QC1Q3%Q8231%Q:3QB1;&@z%221C&A&?+T0%22@1&C+2+R0%3221%8251%<2;F&B+4%221Q7%<2E1%>217%B2AGr?%726I%A221%C21<'2%H2QJ5%I26N%3221+Q8%E2D1%J2:1%N2M;%L2<E%9221&9&>rGrE%44321Q0&8rHrF+@%Q6221u8rB%75;6321':&<vHrJ+Zkb8%RK3S71RI/01S7rI%756521?&=%RK2S<<%238RN1+;%S33SA1S1rD%QF2QEQE%QA221%QK2K1%S32SD1%:3861+=%S;3SI1S9%S72SHQ0%>3421+>%S?3SM1S=%S;2SL<%B3421+?%SC3T11SA&DrC%221B%R221B%SC2T41%J3861%R>2Q:3%SF2T71%M33S31+ZkX0%SN3T:1SL/01T:&7%RE2QFQ@%24Q?Q51<%Q<5Q;741QD%Q>3QJQ61p0Q@1p0QI1p0QO1p0R31p0R71p0R<1p0RA1p0RC1p0RI1p0RK1p0S51p0S91p0S?1p0SE1p0SM1p0T51p0T=1pQ<TJ1pQJTK1pQFTL1pQ>TM1pQ@TN1pQLTO1pR0U11p>U21pQNU81").
Proof.
intros regs M rom r fa chp n nf2 a0v H10 H8 H18 H20 H21 H22 Hr Hr' Hfa Hfa' Hchp Hchp' Hn Hnf Ha0 Wr Cnf.
zbft (ltac:(oF' 0x56e48%Z)) (ltac:(oD' 0x56e48%Z)).
zld (ltac:(oF' 0x56e4c%Z)) (ltac:(oD' 0x56e4c%Z)) (r + 16) Cnf.
zstep (ltac:(oF' 0x56e50%Z)) (ltac:(oD' 0x56e50%Z)).
zbft (ltac:(oF' 0x56e54%Z)) (ltac:(oD' 0x56e54%Z)).
zstep (ltac:(oF' 0x56e58%Z)) (ltac:(oD' 0x56e58%Z)). zstep (ltac:(oF' 0x56e5c%Z)) (ltac:(oD' 0x56e5c%Z)).
zsd (ltac:(oF' 0x56e60%Z)) (ltac:(oD' 0x56e60%Z)) (r + 16) (nf2 - n) ltac:(rewok Wr).
zstep (ltac:(oF' 0x56e64%Z)) (ltac:(oD' 0x56e64%Z)).
stepn (ltac:(oF' 0x56e68%Z)) (ltac:(oD' 0x56e68%Z)).
zstep (ltac:(oF' 0x56cf0%Z)) (ltac:(oD' 0x56cf0%Z)). zstep (ltac:(oF' 0x56cf4%Z)) (ltac:(oD' 0x56cf4%Z)). zstep (ltac:(oF' 0x56cf8%Z)) (ltac:(oD' 0x56cf8%Z)). zstep (ltac:(oF' 0x56cfc%Z)) (ltac:(oD' 0x56cfc%Z)).
zret.
Qed.
End FPX.
