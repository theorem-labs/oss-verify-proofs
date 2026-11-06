(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk ArtMem JbtFp JbtCellEx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtByteCell () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1option"; "2and"; "2eq"; "2iff"; "2or"; "3Z"; "0M"; "4cell"; "5seg_rom"; "6loaded_segments"; "7le"; "7lt"; "7pow"; "0a"]; ["8Z_to_bv"; "8bv"; "8bv_unsigned"; "0v"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_seg_rom_off : ltac2:(TCodec.tc2 tcn__JbtByteCell "L'AyR0%211'6&=&Br1%2261+RPP0%5221&<+Vb\P0%2215%:241'4'2y8%A11%311&:&;r2%3221(0%117%;3731p0=1pQ:I1").
Proof.
intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
rewrite (art_find_segment_none ASEGS 0x10000 0x693000 (U x) art_asegs_in Hx). reflexivity.
Qed.
Lemma art_byte_of_cell1 : ltac2:(TCodec.tc2 tcn__JbtByteCell "QF'AyR0%211'2y8%511%311p051'7'6&=r2+RPP0%3221&<+Vb\P0%2215%8241'3zr3%7221&>+2+R0%3221%@261%9261+X0%C291%<291&9&;r6r5u1r4%6554321'4r7&@%12Q88%311(1%42Q8:%22Q81%83Q841p0:1p0B1p0F1p0Q11pQ8Q;1pQ0Q<1pBQ>1").
Proof.
intros M a v Ha Ha' Hv C. unfold cell in C. cbn [rdn] in C. rewrite art_bytes1 in C by lia.
destruct (M (Z_to_bv 64 a)) as [b|] eqn:E.
- injection C as C. rewrite C. reflexivity.
- rewrite art_seg_rom_off in C by (rewrite art_u_lit by lia; exact Ha). discriminate C.
Qed.
Lemma art_cell1_iff_byte : ltac2:(TCodec.tc2 tcn__JbtByteCell "QF'AyR0%211'2y8%511%311p051'7'6&=r2+RPP0%3221&<+Vb\P0%2215%8241'3zr3%7221&>+2+R0%3221%@261%9261+X0%C291%<291&5&9&;r6r5u1r4%6554321'4&@%12Q86%811(1%42Q87%22Q81%73Q841%@291p0B1p0F1p0Q11pQ8Q;1pQ0Q<1pBQ>1").
Proof. intros M a v Ha Ha' Hv. split; [apply art_byte_of_cell1; assumption|apply art_cell1_of_byte; exact Hv]. Qed.
