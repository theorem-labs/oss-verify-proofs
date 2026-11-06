(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_BigLinkZA () := "C56Stdlib6NArith6BinNat1N4succI47Corelib4Init5Logic2eq00C56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3addC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes3nat02C56Stdlib6NArith4Nnat5N2Nat8inj_succC47Corelib4Init5Logic6eq_indC47Corelib4Init5Peano9plus_n_SmI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1N00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1N01C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03".
Open Scope Z_scope.

Lemma za_step (P : nat -> Prop) (i i' : N) :
  N.succ i = i' -> P (N.to_nat i) -> (forall j, P (N.to_nat i' + j)%nat) -> forall j, P (N.to_nat i + j)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_BigLinkZA ()) [] "p'0h01jh12HSh22i'h31ni001nh41Ph51ih61Hh72H0h82j0p;1p;3p;2p;6g0000j12Tg000Nj3:Tg000hj10Tg001Hj21Tg001_j29Tg002?j18Tg002cj67Tg003Aj13Tg003`j16Tg004Dj64Tg004`j25Tg005?R0p-0[R1g005^R2f1R3#2f0R45:2P2f2R5#2f4R6f3R7#0O1f6R8%05R9/14O1^00f7R:%08/14O1R8^00[[X22P7P9O1f5R9%26#0/14O1^00P0P8P4P0%09R9P:P4O1X30P5g006<,99%89E7P7P4O1f8R7%2:#0/14O1P0%27#0f:1145O1X30P4%07#3R:%67E4f9R711:3O1P0%07R7/15#3f;P4O1X30P4%35,171575E4b1b1X00P4O1n0110000020010100X80W1W7P3P4E4W6X22X52X41P5P3P4O3X22W5W4o"). Qed.

Lemma za_start (P : nat -> Prop) : (forall j, P (N.to_nat 0 + j)%nat) -> forall j, P j.
Proof.
ltac2:(KReplay.run1 (kr_t_BigLinkZA ()) [] "h01Ph11jh21Hp;1p;2g000hj11Tg001Hj20Tg005?R0p-0[R1f1R2g006[#1f0R3'0O1^10P2P3O1X10W2X01P3O1W0o"). Qed.

Lemma za_lit a : 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
ltac2:(KReplay.run1 (kr_t_BigLinkZA ()) [] "h01ah11Hh21zp;2p;1p;3p;6g0079j2>Tg007Uj10Tg008:j11Tg008Xj22Tg0095j2=Tg009Qj2:Tg009lj14Tg00:Jj23Tg000Nj35Tg00;0j16Tg00;Yj37Tg00<<j28Tg00<bj29Tg00=Lj2<Tg002cj6;Tg00>;R0g00>Yf0R1'>g00?7#0R2#1%02#0#0#0#0R2#1'2,=1':P0%42R2f1R3'3f29501X20%62=7311823,921<23E;W1X00P1O1W0o"). Qed.

(* [comment removed for export] *)
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
(* [comment removed for export] *)
Ltac za_tac Vz K :=
  lazymatch goal with
  | |- forall j, @?P j => let Pn := fresh "PZA" in pose (Pn := P); refine (za_start Pn _); za_loop Pn Vz K 0%N
  end.
(* [comment removed for export] *)
Ltac za_tac0 K :=
  lazymatch goal with
  | |- forall j : nat, bv_unsigned (?f j) = @?F j =>
      let Vz := fresh "VZA" in pose (Vz := F);
      change (forall j : nat, bv_unsigned (f j) = Vz j); za_tac Vz K
  end.
