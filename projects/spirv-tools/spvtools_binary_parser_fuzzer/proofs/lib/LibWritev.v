(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  RelSpec SimInv ExitSim CatSim CatExec PropExec SeqExec Hoare ShapeAlg Nodes FileSim AgentLib AgentNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LibWritev () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions=bv_wrap_smallC47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeI47Corelib7Numbers7BinNums1N00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma word_to_nat_Z : forall z, (0 <= z < 2^64)%Z -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof.
ltac2:(KReplay.run1 (kr_t_LibWritev ()) [] "h02Hah14__x1h21zh31Hh42H0h52Hzh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__witp;1p;2p;3p;4p;7p;6p;8g0000j12Tg000Uj16Tg0013j2@Tg001Pj21Tg001lR0j25Tg002Gj1GTg002ej2DTg003Kj13Tg003kj34Tg004Ej2<Tg004_j2>Tg005Gj3=Tg005kj1VTg006Kj1UTg006kj2TTg007Ij1MTg007gj1LTg008Rj2KTg0095j29Tg009Xj3FTg00:;j48Tg00:fj1CTg00;Hj7ETg00;lj2BTg00<Nj2HTg00=:j3ATg00=Yj4ITg00>Kj3JTg00?7j6:Tg00?Uj2?Tg00@;j2NTg00@ej2OTg00ATj1PTg00BOj2QTg00Bkj7RTg00COj8STg00D3R1f0R2'Qp=0f1R3g00DQR4g00E0R5P5g00EPR6P2g00F0FRp=;f3R7P4P5P5P6f2R8P3P2GSp=7g00FPR9%02g00FnR:#2R;#6R<%2;#2#2#2#2R;#6R='@R>,12R?'5P9%G;R;/D3R@g00GSRA%32%3834X29RBP9P3PB%33RB,<AP@1><=111<%0=111>[[%0<R@g00H2RCA=<=3UW0%0>\C^0@P0%07117>f4R7#0117>'5P8f5#0f6/1>g00HNR7#V%U71T93%M9%L9R7P91K9:R:g00I:199<=F9;C8,;7R<%C5R0P7P91991g00IaP:C8,;7R:P0P7P4P5P5P6P:P<FEC7C71B76P2P8g00JHR7g00JhR6'<1H28=476dAA913CIb7b:b;X19%03%08118>'5[\?^19P2f8P3P8O3b6W4W3P3P2O2n2001000000121000000b8b99J;3E:1?;3R2,N;1O;3E:%P2=4ABeW5W2o"). Qed.

Lemma u64_roundtrip' : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_LibWritev ()) [] "h02b1h12b2h21nh31Hh41xh51zp;1p;3p;2p;6g0000j13Tg002Gj1;Tg00KHj11Tg003kj32Tg00@;j20Tg00Kkj3:Tg00?Uj29Tg002ej25Tg00LOj26Tg00>Kj37Tg00@ej24Tg00?7j68Tg00Fn#3#3#3#3#3#3#;R0#1g00MBR1f0R2#1R3f1R4#1R5g001lf2R6#1?242g00FPR7f3R8/06108432R9[10641062527%18?264[R:f4#1?286\9A:642P2n2001000000120000000W1W0W2P:^15^03^21P2P01004R1,90R3P4P7150110069272X571604970110031401E8O4b3W4o"). Qed.

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.

Fixpoint iov_array (mem : word -> option byte) (iov : word) (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r =>
      rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b)
      /\ rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n)
      /\ (bv_unsigned n < 2 ^ 63)%Z
      /\ iov_array mem (Z_to_bv 64 (bv_unsigned iov + 16)) r
  end.

Fixpoint iov_bufs (mem : word -> option byte) (iovs : list (word * word)) (bss : list (list byte)) : Prop :=
  match iovs, bss with
  | [], [] => True
  | (b, n) :: r, bs :: bss' => rdn segs mem b (word_to_nat n) = Some bs /\ iov_bufs mem r bss'
  | _, _ => False
  end.

End WithSegs.
