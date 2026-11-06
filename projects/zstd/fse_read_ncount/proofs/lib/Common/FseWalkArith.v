(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
Import ListNotations.
Open Scope Z_scope.
Lemma sraiw31_sign : forall c, - 2147483648 <= c < 2147483648 ->
bv_swrap 32 (Z.shiftr (bv_swrap 32 (c mod 18446744073709551616)) 31) = (if c <? 0 then -1 else 0).
Proof.
intros c Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0060=1641691110.3 21918288674.22807064488.3 61933545449.364097424.2   7224928843.2 00000600:00@00F00J00KS2Hc1HS2HcS2Hc1HS2Hc1HS2HcS".
rewrite (swrap32_eqm (c mod 18446744073709551616) c) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2^31) with 2147483648.
destruct (Z.ltb_spec c 0); rewrite swrap32_small; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma lxor_sign_mod : forall a, - 9223372036854775808 <= a < 9223372036854775808 ->
Z.lxor (a mod 18446744073709551616) 9223372036854775808 = a + 9223372036854775808.
Proof.
intros a Ha. change 9223372036854775808 with (2^63) at 2. Local Ltac2 Set LiaHints.tbl := fun () => "0020=12840669021.238948406330.2000004005S2HaS".
rewrite zb_lxor_sign by (apply Z.mod_pos_bound; lia).
change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma slt_lit_rr : forall a b, - 9223372036854775808 <= a < 9223372036854775808 -> - 9223372036854775808 <= b < 9223372036854775808 ->
(Z.lxor (a mod 18446744073709551616) 9223372036854775808 <? Z.lxor (b mod 18446744073709551616) 9223372036854775808) = (a <? b).
Proof.
intros a b Ha Hb. Local Ltac2 Set LiaHints.tbl := fun () => "0040=21270332905.522124252747.429306103519.451894210119.500000300700;00>S1HS2HbS2HaS1H".
rewrite !lxor_sign_mod by lia.
destruct (Z.ltb_spec a b); [apply Z.ltb_lt| apply Z.ltb_ge]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma slt_lit_mr : forall a b, - 9223372036854775808 <= a < 9223372036854775808 -> 0 <= b < 9223372036854775808 ->
(Z.lxor (a mod 18446744073709551616) 9223372036854775808 <? Z.lxor b 9223372036854775808) = (a <? b).
Proof.
intros a b Ha Hb. Local Ltac2 Set LiaHints.tbl := fun () => "0030=22124252747.429306103519.450363210057.400000400800<S2HbS2HaS2Hb".
rewrite <- (Z.mod_small b 18446744073709551616) at 1 by lia. apply slt_lit_rr; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma mask_sel : forall (b : bool) y,
Z.land ((Z.b2z b + -1) mod 18446744073709551616) (y mod 18446744073709551616) = (if b then 0 else y mod 18446744073709551616).
Proof.
intros [|] y; cbn [Z.b2z].
- reflexivity.
- change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "0020=18932239167.135496346213.1000001002SS".
rewrite Z.land_comm, Z.land_ones by lia.
change (2^64) with 18446744073709551616. apply Z.mod_mod. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma container_add : forall X bs c2 bc, 0 <= bc < 32 -> X mod 2^32 = bs ->
((bv_swrap 32 (Z.shiftl (c2 mod 18446744073709551616) (bc mod 32)) + X) mod 2^64) mod 2^32 = u32 (bs + u32 (u32 c2 * 2 ^ bc)).
Proof.
intros X bs c2 bc Hbc <-. Local Ltac2 Set LiaHints.tbl := fun () => "0020=18928846753.440136305770.4000001006SS3Hbc".
rewrite shiftl_mod32 by lia. unfold u32.
change (2^64) with 18446744073709551616. change (2^32) with 4294967296.
rewrite mod64_mod32. rewrite Z.add_mod by lia. rewrite swrap32_mod32.
rewrite (Z.mul_mod (c2 mod 18446744073709551616)) by lia. rewrite mod64_mod32.
rewrite <- (Z.mul_mod c2) by lia. rewrite (Z.add_mod (X mod 4294967296)) by lia.
rewrite (Z.mul_mod (c2 mod 4294967296)) by lia. rewrite !Z.mod_mod by lia.
rewrite <- (Z.mul_mod c2) by lia. rewrite (Z.add_comm (X mod 4294967296)). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land_1_mod2 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). Local Ltac2 Set LiaHints.tbl := fun () => "0010<6757220598.1000001S".
rewrite Z.land_ones by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma abs_via_sign : forall rem c, - 2147483648 <= c < 2147483648 -> - 2147483648 <= rem - (if c <? 0 then - c else c) < 2147483648 ->
0 <= rem < 4294967296 ->
bv_swrap 32 ((rem + (if c <? 0 then -1 else 0)) mod 18446744073709551616
- Z.lxor (c mod 18446744073709551616) ((if c <? 0 then -1 else 0) mod 18446744073709551616))
= rem - (if c <? 0 then - c else c).
Proof.
intros rem c Hc Hr Hrem. destruct (Z.ltb_spec c 0).
- change ((-1) mod 18446744073709551616) with 18446744073709551615.
Local Ltac2 Set LiaHints.tbl := fun () => "0040=38954701265.639536164997.642130722670.648189864791.600000100500=00ASS2HrS1H4HremS2Hr".
rewrite zb_lxor_ones by (apply Z.mod_pos_bound; lia). apply swrap32_eqm; lia.
- change (0 mod 18446744073709551616) with 0. rewrite Z.lxor_0_r. apply swrap32_eqm; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
