(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_KStep () := ([""; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1and"; "1eq"; "2Z"; "3page_round_up_Z"; "3page_size"; "0RUNp"; "4mmap_len"; "5alloc_ceiling"; "6ehi"; "6elo"; "6went"; "6wz"; "7PGSZ"; "7round_up_pg"; "8add"; "8land"]; ["8le"; "8lt"; "8modulo"; "8pow"; "0b"; "0l"; "0n"; "9bv_unsigned"; "0x"; "0z"]]).
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma PGSZ_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep "5'1'2&<+TP0%43321"). Proof. reflexivity. Qed.
Lemma page_size_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep "5'1'2&4+TP0%43321"). Proof. reflexivity. Qed.
Lemma land_4095 : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep ";'2'1&?r1+SoO%3221&B+TP0%2251%83941pQB:1").
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma round_up_pg_aligned : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep ">'2'1&Br1+TP0%3221z%63721&=r2%211%:3;12p051pQB=1").
Proof.
intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
assert ((- x) mod 4096 = 0). { apply Z.mod_opp_l_z; lia. } lia.
Qed.
Lemma round_up_pg_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep "9'2'1&=r1%211&3%113%63731pQB81").
Proof.
intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
nia.
Qed.
Lemma mmap_len_ge : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep "B'2&Azr1%3221'0&@r2&6%112%4231&>+TP0%2261%=251%:251p0<1pQ<A1").
Proof. intros. apply mmap_len_bound. assumption. Qed.
Lemma mmap_len_aligned : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep ";'2'1&B&6r1%211+TP0%5221z%83921pQ<:1").
Proof. intros. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. apply Z_mod_mult. Qed.
Lemma mmap_len_of_aligned : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep "B'2&@zr1%3221'1&Br2+TP0%3221%53:18&6r3%211%93>12p051p0<1pQ<A1").
Proof. intros l Hl Ha. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full l 4096). pose proof (Z_div_mod_eq_full (l + 4095) 4096). pose proof (Z.mod_pos_bound (l+4095) 4096). nia. Qed.
Lemma unsigned_wz : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep "G'2'0&@zr1%3221&A&C+2+R0%3221%5271%;271'1&GyR0&;r2%211%5241%73D13p091pQDF1").
Proof. intros. unfold wz. apply unsigned_lit. assumption. Qed.
Lemma alloc_ceiling_lt : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep "9&A&7v5%211&C+2+QO%3221%8251").
Proof. pose_ceil. lia. Qed.
Lemma elo_went : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep "G'2'0&@zr2%3221&A&C+2+R0%3221%5271%;271'1&9&:r3%221=%411%63C13p081pQ>E1pQ:F1").
Proof. intros. unfold elo, went. cbn [fst]. apply unsigned_wz. assumption. Qed.
Lemma ehi_went : ltac2:(TCodec.tc2 tcn__CJ_Spec_KStep "K'2'0&@zr2%3221&A&C+2+R0%3221%5271%;271'1&8&:r4r3%3221%511&>%1254%93F31p0;1p0<1pQ>I1pQ:J1").
Proof. intros. unfold ehi, went. cbn [fst snd]. rewrite !unsigned_wz by assumption. reflexivity. Qed.
End CEIL_WRAP_1.
