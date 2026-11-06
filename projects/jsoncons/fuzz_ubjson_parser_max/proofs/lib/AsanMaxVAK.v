(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia Bool Btauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanMaxVAK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMaxVAK."; "Stdlib.ZArith.BinInt.Z."], [["1bool"; "1orb"; "2and"; "2eq"; "3Z"; "4maxva_tail"; "4ones_from"; "4smear6"; "4smear_step"; "5add"; "5le"; "5lt"; "5pow"; "5sub"; "5testbit"; "0lo"]; ["0n"; "0s"; "0v"; "0x"]]).
#[global] Unset Lia Cache.
#[global] Unset Nia Cache.
#[global] Unset Nra Cache.
Open Scope Z_scope.
Definition smear_step (s : Z) (x : Z) : Z := Z.lor x (Z.shiftr x s).
Definition smear6 (x : Z) : Z :=
smear_step 32 (smear_step 16 (smear_step 8 (smear_step 4 (smear_step 2 (smear_step 1 x))))).
Lemma smear_step_nonneg : ltac2:(TCodec.tc2 tcn__AsanMaxVAK ">'4&:zr2%3221&8r4r3%3221%8271p061p071pQ8<1pQ4=1").
Proof. intros s x. intros Hs Hx. unfold smear_step. apply Z.lor_nonneg. split; [exact Hx| apply Z.shiftr_nonneg; exact Hx]. Qed.
Lemma smear_step_spec : ltac2:(TCodec.tc2 tcn__AsanMaxVAK "K'4&:zr3%3221r2%5241'3'0&>&8r5r4%3221%521;&1%724=&9%12?7%:271%5241%>3=71p0@1p0C1pQ2H1pQ8I1pQ4J1").
Proof. intros s x n. intros Hs Hn. unfold smear_step. rewrite Z.lor_spec, Z.shiftr_spec by lia. reflexivity. Qed.
Definition ones_from (lo : Z) (v : Z) : Prop :=
0 <= v /\ (forall n, 47 <= n -> Z.testbit v n = false) /\ (forall n, 0 <= n -> lo <= n <= 46 -> Z.testbit v n = true).
Lemma ones_step : ltac2:(TCodec.tc2 tcn__AsanMaxVAK "I'4&:zr3%3221&9r4%2241+Q?%8221&6%1258&=r5r6%3221&8%123;%8231p081p0;1p0A1pQ6F1pQ0G1pQ4H1").
Proof. intros s lo v.
intros Hs Hlen (Hv & Hhi & Hlo). split; [apply smear_step_nonneg; assumption|]. split.
- intros n Hn. rewrite smear_step_spec by lia. rewrite Hhi by lia. rewrite Hhi by lia. reflexivity.
- intros n Hn0 Hn. rewrite smear_step_spec by lia.
destruct (Z_le_gt_dec lo n) as [H|H].
+ rewrite (Hlo n) by lia. reflexivity.
+ rewrite (Hlo (n + s)) by lia. apply orb_true_r.
Qed.
Lemma ones_start : ltac2:(TCodec.tc2 tcn__AsanMaxVAK "C'4'2&:&<+2+Q>%3221r1%6221&;+Q?%8271%3251%<251&6r2%22;1p041pQ8B1").
Proof. intros x.
intros Hx. split; [lia|]. split.
- intros n Hn. destruct (Z.testbit x n) eqn:E; [|reflexivity]. exfalso.
apply Z.testbit_true in E; [|lia].
assert (2 ^ 47 <= 2 ^ n) by (apply Z.pow_le_mono_r; lia).
assert (x / 2 ^ n = 0) by (apply Z.div_small; lia). rewrite H0 in E. cbn in E. lia.
- intros n Hn0 Hn. assert (n = 46) by lia. subst n.
apply Z.testbit_true; [lia|].
assert (x / 2 ^ 46 = 1) as ->; [| reflexivity].
symmetry. apply Z.div_unique with (r := x - 2 ^ 46); lia.
Qed.
Lemma ones_all : ltac2:(TCodec.tc2 tcn__AsanMaxVAK "A'4&6zr1%3221'3r2&=&<+2+Q?%3221+1%6221%93>81p0;1pQ6@1").
Proof. intros v.
intros (Hv & Hhi & Hlo).
replace (2 ^ 47 - 1) with (Z.ones 47) by (rewrite Z.ones_equiv; reflexivity).
apply Z.bits_inj'. intros n Hn.
destruct (Z_lt_le_dec n 47) as [H|H].
- rewrite Hlo by lia. rewrite Z.ones_spec_low by lia. reflexivity.
- rewrite Hhi by lia. rewrite Z.ones_spec_high by lia. reflexivity.
Qed.
Theorem smear6_eq : ltac2:(TCodec.tc2 tcn__AsanMaxVAK "H'4'2&:&<+2+Q>%3221r1%6221&;+Q?%8271%3251%<251'3&7r2%211&=+1%2291%73E41p091pQ8G1").
Proof. intros x.
intros Hx. apply ones_all. unfold smear6.
replace 0 with (46 - 1 - 2 - 4 - 8 - 16 - 32 + 17) by lia.
assert (M : forall lo lo' v, lo <= lo' -> lo <= 0 \/ lo <= lo' -> ones_from lo v -> ones_from lo' v).
{ intros lo lo' v H _ (A & B & C). split; [exact A|]. split; [exact B|]. intros n Hn0 Hn. apply C; lia. }
apply (M (46 - 1 - 2 - 4 - 8 - 16 - 32)); [lia| lia|].
apply ones_step; [lia| lia|]. apply ones_step; [lia| lia|]. apply ones_step; [lia| lia|].
apply ones_step; [lia| lia|]. apply ones_step; [lia| lia|]. apply ones_step; [lia| lia|].
apply ones_start. exact Hx.
Qed.
Definition two64 : Z := 2 ^ 64.
Definition w64 (z : Z) : Z := z mod two64.
Definition maxva_tail (y : Z) : Z :=
let a0 := w64 (Z.lnot y) in
let a5 := Z.shiftr a0 1 in
let a1 := Z.land a5 0x5555555555555555 in
let a0 := w64 (a0 - a1) in
let a1 := Z.land a0 0x3333333333333333 in
let a0 := Z.shiftr a0 2 in
let a0 := Z.land a0 0x3333333333333333 in
let a0 := w64 (a1 + a0) in
let a1 := Z.shiftr a0 4 in
let a0 := w64 (a0 + a1) in
let a0 := Z.land a0 0x0f0f0f0f0f0f0f0f in
let a0 := w64 (a0 * 0x0101010101010101) in
let a0 := Z.shiftr a0 56 in
let a0 := w64 (- (a0 mod 2 ^ 32)) in
let a1 := w64 (-1) in
let a0 := w64 (Z.shiftl a1 (a0 mod 64)) in
w64 (Z.lnot a0).
Lemma maxva_tail_const : ltac2:(TCodec.tc2 tcn__AsanMaxVAK "<'3'4&5&=&<+2+Q?%3221+1%6221%811%;3:12").
Proof. vm_compute. reflexivity. Qed.
Theorem maxva_eq : ltac2:(TCodec.tc2 tcn__AsanMaxVAK "J'4'2&:&<+2+Q>%3221r1%6221&;+Q?%8271%3251%<251'3&5&7r2%211%411&=+1%22;1%93G41p0;1pQ8I1").
Proof. intros x. intros Hx. rewrite (smear6_eq x Hx). exact maxva_tail_const. Qed.
