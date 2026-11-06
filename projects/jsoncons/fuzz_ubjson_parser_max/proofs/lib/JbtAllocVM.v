(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk ArtMem ArtRegs ArtAtomics ArtTac JbtAllocV.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocVM () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocV."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2and"; "2eq"; "2not"; "3Z"; "0M"; "4apart"; "4cell"; "5art_e_mem"; "6loaded_segments"; "7add"; "7le"; "7lt"; "7modulo"; "7pow"; "7sub"]; ["0ab"; "0b1"; "0n"; "0rz"; "0sp"; "8bv"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
Lemma art_e_magic : ltac2:(TCodec.tc2 tcn__JbtAllocVM "R:'EyR0%211'0y8%511%311p051'4&;+Q0r5%3221&<r6&>+2+R0%3221%6251z%<217&:r7%221:%<217+@%B214&3'2r8%23G15%411&=r9%2219%73L1@&6&?r<%221Nr;%542Q01@'1&7&9&8r>r=r:%4632;91@u8+\hkdfgWVVmUeI%9583>21+8%Q12@1%Q22A?%C21O%>5=8371%@261p0B1p0I1p0N1p0Q41p0Q71p0Q<1p0Q?1p0QG1pQ4QL1pQ6QM1pQ8QN1pQ2QO1pQ:R01p<R21").
Proof.
intros M sp ab rz n b1 Hsp Hsp' Hab Hab' Hrz Nrz Mrz A. unfold art_e_mem.
destruct (Z.eqb_spec rz 16) as [E|_]; [contradiction|].
assert (H32 : 32 <= rz). { pose proof (Z.div_mod rz 16 ltac:(lia)) as D. rewrite Mrz in D. lia. }
split; zcell.
Qed.
