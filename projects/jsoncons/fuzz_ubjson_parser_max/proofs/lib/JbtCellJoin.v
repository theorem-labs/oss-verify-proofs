(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim SeqExec StoreOk ArtMem JbtUnwind.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtCellJoin () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "1option"; "2and"; "3add"; "4le"; "5Z"; "0M"; "6cell"; "7loaded_segments"; "8add"; "8le"; "8lt"; "8mul"; "8of_nat"; "8pow"; "0a"]; ["0b1"; "0h"; "0hi"; "0lo"; "0n1"; "0n2"; "0st"; "9bv"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
Lemma art_cell_join : ltac2:(TCodec.tc2 tcn__JbtCellJoin "R9'GyR0%211'1y8%511%311p051'5'0&:zr5%3221&;&9r6&=&3r4%2281%411%7261&>+2+R0%3221%=251'4%;2=Au8%3221'2&<+8r7%C11%4231%?2>1%I2K1%82K1&7&8r;r:r9%554321;r<%O14%Q2261%958315?r=%Q2298r8%Q51;%F2E1%Q12Q01%H241%Q;2=1%B5A8<71p0:1p0?1p0F1p0G1p0Q11p0Q61p0QE1pQ6QK1pQ8QL1pQ<QL1pQ:QM1pQ0QO1p>R11").
Proof.
intros M a n1 n2 lo hi Ha Ha' Hn Hlo Hhi C1 C2. unfold cell in *.
assert (P1 : 0 < 2 ^ (8 * Z.of_nat n1)) by (apply Z.pow_pos_nonneg; lia).
assert (B1 : 2 ^ (8 * Z.of_nat n1) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
assert (B2 : 2 ^ (8 * Z.of_nat n2) * 2 ^ (8 * Z.of_nat n1) <= 2 ^ 64).
{ rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
assert (Hv : 0 <= lo + hi * 2 ^ (8 * Z.of_nat n1) < 2 ^ 64) by nia.
erewrite rdn_app; [|exact C1|].
2: { replace (Z_to_bv 64 a + nat_to_word n1)%bv with (Z_to_bv 64 (a + Z.of_nat n1) : word); [exact C2|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (Z.mod_small (Z.of_nat n1)) by lia. rewrite (Z.mod_small a) by lia. rewrite Z.mod_small by lia. reflexivity. }
f_equal. unfold word_to_le_bytes. rewrite !art_u_lit by lia. rewrite (Z_to_le_bytes_add n1 n2). f_equal.
- rewrite <- (Z_to_le_bytes_wrap n1 (N.of_nat (8 * n1)) (lo + hi * 2 ^ (8 * Z.of_nat n1))) by lia.
rewrite <- (Z_to_le_bytes_wrap n1 (N.of_nat (8 * n1)) lo) by lia. f_equal.
unfold bv_wrap, bv_modulus. replace (Z.of_N (N.of_nat (8 * n1))) with (8 * Z.of_nat n1) by lia. rewrite Z.mod_add by lia. reflexivity.
- f_equal. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma art_hdr_word : ltac2:(TCodec.tc2 tcn__JbtCellJoin "QL'GyR0%211'1y8%511%311p051'5&:zr3%3221&;&9r4+4%3221&>+2+R0%3221%9251'2%?2>9+X0%=2;1%4231&7&8r8r7u1r6%6554321r9+1%G271%:593165r:%J25Eu2%>5=321Q0r;u4&<%12E@%Q12<1%D5C5941p071p0<1p0A1p0I1p0J1p0Q01p0Q;1pQ2Q@1pQ>QA1pQ4QB1p>QD1").
Proof.
intros M h st b1 Hh Hh' Hst Hb1 C0 C1 C2.
assert (C12 : cellA M (h + 1) 3 (b1 + 0 * 2 ^ (8 * Z.of_nat 1))).
{ apply (art_cell_join M (h + 1) 1 2 b1 0); [lia|cbn; lia|lia|cbn; lia|cbn; lia|exact C1|]. replace (h + 1 + Z.of_nat 1) with (h + 2) by lia. exact C2. }
replace (b1 + 0 * 2 ^ (8 * Z.of_nat 1)) with b1 in C12 by lia.
replace (st + 256 * b1) with (st + b1 * 2 ^ (8 * Z.of_nat 1)) by (cbn; lia).
apply (art_cell_join M h 1 3 st b1); [lia|cbn; lia|lia|cbn; lia|cbn; lia|exact C0|]. replace (h + Z.of_nat 1) with (h + 1) by lia. exact C12.
Qed.
