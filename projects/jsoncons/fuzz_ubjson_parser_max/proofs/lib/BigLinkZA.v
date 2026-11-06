(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__BigLinkZA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Numbers.BinNums."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "2and"; "2eq"; "3add"; "4N"; "4Z"; "0P"; "5succ"; "5to_nat"; "6le"; "6lt"; "6pow"; "0a"; "0i"; "0i'"; "0j"]; ["7Z_to_bv"; "7bv_unsigned"]]).
Lemma za_step : ltac2:(TCodec.tc2 tcn__BigLinkZA "Q0'0!p021'4'2&7r2%211r1%53621r4&8r3%211%411r6&3%617%221:%411pQ0D1r7%;17%721?%311pQ0I1p061p0=1p0C1pNJ1pLK1p>M1").
Proof. intros P i i'.
intros <- H0 HS [|j].
- rewrite Nat.add_0_r. exact H0.
- specialize (HS j). rewrite N2Nat.inj_succ in HS. rewrite <- plus_n_Sm. exact HS.
Qed.
Lemma za_start : ltac2:(TCodec.tc2 tcn__BigLinkZA "A'0!p021r2&3&8w%211r1%5221%711pQ0;1r3%115pQ0>1p041p>>1").
Proof. intros P. intros H j. exact (H j). Qed.
Lemma za_lit : ltac2:(TCodec.tc2 tcn__BigLinkZA "G'5'1&9zr1%3221&:&;+2+R0%3221%5271%;271'2&AyR0&@r2%2231%5241%73D13p091pJF1").
Proof. intros a. intros H. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact H. Qed.
Ltac za_leaf Vz i :=
first [ exact (@eq_refl Z (Vz (N.to_nat i)))
| let a := eval cbv beta iota delta [Vz N.to_nat Pos.to_nat Pos.iter_op Nat.add] in (Vz (N.to_nat i)) in
exact (za_lit a ltac:(split; assumption)) ].
Ltac za_loop P Vz k i :=
lazymatch k with
| O => let j := fresh "j" in intro j; exact (@eq_refl Z (Vz (N.to_nat i + j)%nat))
| S ?k' => let i' := eval vm_compute in (N.succ i) in
refine (za_step P i i' (@eq_refl N i') _ _); [ za_leaf Vz i | za_loop P Vz k' i' ]
end.
Ltac za_tac Vz K :=
lazymatch goal with
| |- forall j, @?P j => let Pn := fresh "PZA" in pose (Pn := P); refine (za_start Pn _); za_loop Pn Vz K 0%N
end.
Ltac za_tac0 K :=
lazymatch goal with
| |- forall j : nat, bv_unsigned (?f j) = @?F j =>
let Vz := fresh "VZA" in pose (Vz := F);
change (forall j : nat, bv_unsigned (f j) = Vz j); za_tac Vz K
end.
