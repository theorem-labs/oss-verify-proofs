(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac AsanAcct HeapIface HeapIfaceA As0StepLib ArtMem ArtTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtWrapMallocH () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1cons"; "1nil"; "1option"; "2I"; "2eq"; "3Z"; "0H"; "4bvmap"; "0M"; "0R"; "0R'"; "5mrestrict"; "6msteps"; "7regs_preserved"; "8S"]; ["8byte_at"; "9getr"; "9mkst"; ":loaded_segments"; ";In"; "<le"; "<sub"; "0a"; "0fx"; "0r"; "0regs"; "0rom"; "=BV"; "=bv"; "0v"; "0y"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_S_pred : ltac2:(TCodec.tc2 tcn__JbtWrapMallocH "<'6&E&F&?r1%211+1%5221%6242%611%9231pR0;1").
Proof.
intros y. unfold HeapIfaceA.S. pose proof (Z.div_mod y 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as R.
assert (y / 8 - 1 <= (y - 1) / 8); [|lia]. apply Z.div_le_lower_bound; lia.
Qed.
Lemma art_kept_preserved : ltac2:(TCodec.tc2 tcn__JbtWrapMallocH "R?&8y5'MyR0%211%5241'5&Ar1(L+2(4%33;21%6251r2%8213%:3<31%?1@&D(1+3%<3D1:+4%>3F1<+8%@3H1>+9%B3J1@+B%D3L1B+C%F3N1D+D%H3Q01F+E%J3Q21H+F%L3Q41J+G%N3Q61L+H%Q03Q81N+I%Q23Q:1Q0+J%Q43Q<1Q2+K%Q63Q>1Q4(2%11Q0%O3Q131%Q03Q261%Q13Q391%Q23Q4<1%Q33Q5?1%Q43Q6B1%Q53Q7E1%Q63Q8H1%Q73Q9K1%Q83Q:N1%Q93Q;Q11%Q:3Q<Q41%Q;3Q=Q71%Q<3Q>Q:1%Q>3Q?QH1r4%QK21QDr5%QM21QF%QO3R131p061pQDQF1&>r3%2291p041p0QL1pHR81pFR91").
Proof.
intros R R' P2 PK r Hr. unfold callee_saved_idx in Hr. rewrite <- (Z_to_bv_bv_unsigned _ r). set (z := bv_unsigned r) in *. cbn [In] in Hr.
destruct Hr as [<-|Hr]; [exact P2|].
repeat (destruct Hr as [<-|Hr]; [apply PK; cbn [In]; repeat first [left; apply bv_eq; reflexivity|right]|]). destruct Hr.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_malloc_thunk : ltac2:(TCodec.tc2 tcn__JbtWrapMallocH "Q0&8y5'MyR0%211%5241'3y8%611%311p061'=&C&BvHr3(L+_T\@(4%33@21/01@r2r1%:598321+_Tk<%93F17/01F%>5=<165%A3@51pQHC1pDD1pQFJ1").
Proof. intros regs M rom. stepj (ltac:(oF' 0x79190%Z)) (ltac:(oD' 0x79190%Z)). apply mst_refl. Qed.
End FPX.
Lemma art_byte_unrestrict : ltac2:(TCodec.tc2 tcn__JbtWrapMallocH "I'MyR0%211'0p021'3y8%711%311p071'6&@&<r4r3%3221r2r1%73321%83653p021pQN;1pQ@<1pD>1p@D1").
Proof. intros H M a v B. unfold byte_at, mrestrict in *. destruct (H (Z_to_bv 64 a)); [discriminate B|exact B]. Qed.
