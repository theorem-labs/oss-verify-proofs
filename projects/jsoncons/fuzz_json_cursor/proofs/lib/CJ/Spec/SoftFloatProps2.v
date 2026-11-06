(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloatProps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.
Local Ltac dnia := Z.div_mod_to_equations; nia.

Definition mulc_net (aSigHi aSigLo bSigHi bSigLo : Z) : Z * Z * Z * Z :=
  let bLo15 := shl64 bSigLo 15 in
  let bHi15 := Z.lor (shr64 bSigLo 49) (shl64 bSigHi 15) in
  let A1 := Z.lor (shr64 aSigHi 32) 0x10000 in
  let A2 := zext32 aSigHi in
  let A3 := shr64 aSigLo 32 in
  let A4 := zext32 aSigLo in
  let B1 := Z.lor (shr64 (shl64 bSigHi 15) 32) 0x80000000 in
  let B2 := zext32 bHi15 in
  let B3 := shr64 bLo15 32 in
  let B4 := zext32 bLo15 in
  let p13 := mul64 B3 A1 in
  let p23 := mul64 B3 A2 in
  let p24 := mul64 B4 A2 in
  let p33 := mul64 B3 A3 in
  let p43 := mul64 B3 A4 in
  let p44 := mul64 B4 A4 in
  let p11 := mul64 B1 A1 in
  let p14 := mul64 B4 A1 in
  let p21 := mul64 B1 A2 in
  let p22 := mul64 B2 A2 in
  let p41 := mul64 B1 A4 in
  let p31 := mul64 B1 A3 in
  let p34 := mul64 B4 A3 in
  let p42 := mul64 B2 A4 in
  let p12 := mul64 B2 A1 in
  let p32 := mul64 B2 A3 in
  let s2a := add64 p24 p33 in
  let sum1 := add64 p34 p43 in
  let c2a := ltu64 s2a p24 in
  let sum2 := add64 s2a p42 in
  let s3a := add64 p14 p23 in
  let s4a := add64 p31 p13 in
  let c1 := ltu64 sum1 p34 in
  let c2b := ltu64 sum2 s2a in
  let c3a := ltu64 s3a p14 in
  let s3b := add64 s3a p41 in
  let sum5 := add64 p12 p21 in
  let sum1Shr32 := shr64 sum1 32 in
  let sum1Shl32 := shl64 sum1 32 in
  let c4a := ltu64 s4a p31 in
  let sum4 := add64 s4a p22 in
  let sum2Hi := add64 c2a c2b in
  let c3b := ltu64 s3b s3a in
  let sum3 := add64 s3b p32 in
  let c5 := ltu64 sum5 p12 in
  let c1Shl32 := shl64 c1 32 in
  let lo_lo := add64 sum1Shl32 p44 in
  let sum5Shr32 := shr64 sum5 32 in
  let sum5Shl32 := shl64 sum5 32 in
  let c4b := ltu64 sum4 s4a in
  let hh1 := add64 c4a p11 in
  let c3ab := add64 c3a c3b in
  let c3c := ltu64 sum3 s3b in
  let r0c := ltu64 lo_lo sum1Shl32 in
  let sum1Mid := Z.lor sum1Shr32 c1Shl32 in
  let sum3Shr32 := shr64 sum3 32 in
  let sum3Shl32 := shl64 sum3 32 in
  let c5Shl32 := shl64 c5 32 in
  let hh2 := add64 hh1 c4b in
  let m1 := add64 sum4 sum2Hi in
  let sum3Hi := add64 c3ab c3c in
  let r1a := add64 sum2 sum1Mid in
  let sum5MidHi := Z.lor c5Shl32 sum5Shr32 in
  let cm1 := ltu64 m1 sum4 in
  let m2 := add64 m1 sum5Shl32 in
  let cr1a := ltu64 r1a sum2 in
  let sum3HiShl32 := shl64 sum3Hi 32 in
  let r1 := add64 r1a sum3Shl32 in
  let hh3 := add64 hh2 cm1 in
  let cm2 := ltu64 m2 m1 in
  let cr1b := ltu64 r1 r1a in
  let lo_hi := add64 r1 r0c in
  let sum3Mid := Z.lor sum3Shr32 sum3HiShl32 in
  let hh4 := add64 hh3 sum5MidHi in
  let r1Hi := add64 cr1a cr1b in
  let carry := ltu64 lo_hi r1 in
  let hh5 := add64 hh4 cm2 in
  let m3 := add64 m2 sum3Mid in
  let cm3 := ltu64 m3 m2 in
  let m4 := add64 m3 r1Hi in
  let hh6 := add64 hh5 cm3 in
  let cm4 := ltu64 m4 m3 in
  let hi_lo := add64 m4 carry in
  let hh7 := add64 hh6 cm4 in
  let cm5 := ltu64 hi_lo m4 in
  let hi_hi := add64 hh7 cm5 in
  (hi_hi, hi_lo, lo_hi, lo_lo).

Definition mulc_p4 (signHi aExp bExp scale : Z) (w : Z * Z * Z * Z) : Z :=
  let '(hi_hi, hi_lo, lo_hi, lo_lo) := w in
  let expSum := add64 aExp bExp in
  let scaleAdj := scale - 0x3fff in
  let productExponent := expSum + scaleAdj in
  if is_neg64 (shl64 hi_hi 15) then
    let productExponent1 := productExponent + 1 in
    if negb (productExponent1 <? 0x7fff) then mk128 (Z.lor signHi INF_HI) 0
    else mul_finish signHi productExponent1 hi_hi hi_lo lo_hi lo_lo
  else
    let hi_hi1 := Z.lor (shl64 hi_hi 1) (shr64 hi_lo 63) in
    let hi_lo1 := Z.lor (shl64 hi_lo 1) (shr64 lo_hi 63) in
    let lo_hi1 := Z.lor (shl64 lo_hi 1) (shr64 lo_lo 63) in
    let lo_lo1 := shl64 lo_lo 1 in
    if 0x7fff <=? productExponent then mk128 (Z.lor signHi INF_HI) 0
    else mul_finish signHi productExponent hi_hi1 hi_lo1 lo_hi1 lo_lo1.

Lemma mul_core_restage : forall signHi aExp bExp aSigHi aSigLo bSigHi bSigLo scale,
  mul_core signHi aExp bExp aSigHi aSigLo bSigHi bSigLo scale =
  mulc_p4 signHi aExp bExp scale (mulc_net aSigHi aSigLo bSigHi bSigLo).
Proof. intros. unfold mul_core, mulc_p4, mulc_net. cbv zeta. reflexivity. Qed.

Lemma L_mul : forall b a, 0 <= b < 2^32 -> 0 <= a < 2^32 -> mul64 b a = b * a /\ 0 <= b * a < 2^64.
Proof. intros. assert (0 <= b * a < 2^64) by nia. split; [apply mul64_small; lia| lia]. Qed.
Lemma L_addc : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  add64 x y + 2^64 * ltu64 (add64 x y) x = x + y /\ 0 <= add64 x y < 2^64 /\ 0 <= ltu64 (add64 x y) x <= 1.
Proof.
  intros x y Hx Hy. unfold ltu64. rewrite b2z_val, add64_val.
  destruct (Z.lt_ge_cases (x + y) (2^64)).
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec (x + y) x); lia.
  - replace ((x + y) mod 2^64) with (x + y - 2^64).
    2:{ apply Z.mod_unique with (q := 1); lia. }
    destruct (Z.ltb_spec (x + y - 2^64) x); lia.
Qed.
Lemma L_shl32 : forall s, 0 <= s < 2^64 -> shl64 s 32 = (s mod 2^32) * 2^32.
Proof.
  intros. rewrite shl64_val by lia.
  rewrite (Z.div_mod s (2^32)) at 1 by lia.
  replace ((2 ^ 32 * (s / 2 ^ 32) + s mod 2 ^ 32) * 2 ^ 32) with ((s mod 2^32) * 2^32 + (s / 2^32) * 2^64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. pose proof (Z.mod_pos_bound s (2^32)). lia.
Qed.

Local Ltac defbody x := eval cbv delta [x] in x.

Local Ltac nobodies := repeat match goal with x := _ |- _ => clearbody x end.

Inductive boxed (P : Prop) : Prop := box : P -> boxed P.
Local Ltac fact_mul p :=
  lazymatch defbody p with mul64 ?b ?a =>
    let H := fresh "M" p in let R := fresh "R" p in
    assert (H : p = b * a /\ 0 <= b * a < 2^64) by (cbv delta [p]; nobodies; apply L_mul; lia);
    assert (R : 0 <= p < 2^64) by (clear -H; lia);
    apply proj1 in H; apply box in H;
    clearbody p
  end.
Local Ltac fact_addc s c :=
  lazymatch defbody s with add64 ?x ?y =>
    let H := fresh "C" s in
    assert (H : s + 2^64 * c = x + y /\ 0 <= s < 2^64 /\ 0 <= c <= 1) by (cbv delta [s c]; nobodies; apply L_addc; lia);
    clearbody s c
  end.
Local Ltac fact_adds s :=
  lazymatch defbody s with add64 ?x ?y =>
    let H := fresh "S" s in
    assert (H : s = x + y) by (cbv delta [s]; nobodies; apply add64_small; lia);
    clearbody s
  end.
Local Ltac fact_shr s :=
  lazymatch defbody s with Z.shiftr ?x ?k =>
    let H := fresh "R" s in
    assert (H : s * 2^k <= x < s * 2^k + 2^k /\ 0 <= s)
      by (cbv delta [s]; nobodies; rewrite shiftr_div by lia;
          pose proof (Z.div_mod x (2^k) ltac:(lia)); pose proof (Z.mod_pos_bound x (2^k) ltac:(lia));
          split; [lia| apply Z.div_pos; lia]);
    clearbody s
  end.

Local Ltac fact_shl32 s q :=
  lazymatch defbody s with shl64 ?x 32 =>
    let H := fresh "L" s in
    assert (H : s = (x - q * 2^32) * 2^32 /\ 0 <= x - q * 2^32 < 2^32)
      by (cbv delta [s]; nobodies; rewrite L_shl32 by lia;
          replace (x mod 2^32) with (x - q * 2^32) by (apply (Z.mod_unique x (2^32) q); lia); lia);
    clearbody s
  end.
Local Ltac fact_shl_small s :=
  lazymatch defbody s with shl64 ?x ?k =>
    let H := fresh "L" s in
    assert (H : s = x * 2^k) by (cbv delta [s]; nobodies; apply shl64_small; lia);
    clearbody s
  end.

Lemma mulc_net_val : forall tha tla thb tlb,
  0 <= tha < 2^48 -> 0 <= tla < 2^64 -> 0 <= thb < 2^48 -> 0 <= tlb < 2^64 ->
  let '(hh, hl, lh, ll) := mulc_net tha tla thb tlb in
  0 <= hh < 2^64 /\ 0 <= hl < 2^64 /\ 0 <= lh < 2^64 /\ 0 <= ll < 2^64 /\
  hh * 2^192 + hl * 2^128 + lh * 2^64 + ll = (2^112 + tha * 2^64 + tla) * ((2^112 + thb * 2^64 + tlb) * 2^15).
Proof.
  intros aSigHi aSigLo bSigHi bSigLo Htha Htla Hthb Htlb.
  unfold mulc_net. cbv zeta.
  set (bLo15 := shl64 bSigLo 15).
  set (bHi15 := Z.lor (shr64 bSigLo 49) (shl64 bSigHi 15)).
  set (A1 := Z.lor (shr64 aSigHi 32) 0x10000).
  set (A2 := zext32 aSigHi).
  set (A3 := shr64 aSigLo 32).
  set (A4 := zext32 aSigLo).
  set (B1 := Z.lor (shr64 (shl64 bSigHi 15) 32) 0x80000000).
  set (B2 := zext32 bHi15).
  set (B3 := shr64 bLo15 32).
  set (B4 := zext32 bLo15).
  set (p13 := mul64 B3 A1).
  set (p23 := mul64 B3 A2).
  set (p24 := mul64 B4 A2).
  set (p33 := mul64 B3 A3).
  set (p43 := mul64 B3 A4).
  set (p44 := mul64 B4 A4).
  set (p11 := mul64 B1 A1).
  set (p14 := mul64 B4 A1).
  set (p21 := mul64 B1 A2).
  set (p22 := mul64 B2 A2).
  set (p41 := mul64 B1 A4).
  set (p31 := mul64 B1 A3).
  set (p34 := mul64 B4 A3).
  set (p42 := mul64 B2 A4).
  set (p12 := mul64 B2 A1).
  set (p32 := mul64 B2 A3).
  set (s2a := add64 p24 p33).
  set (sum1 := add64 p34 p43).
  set (c2a := ltu64 s2a p24).
  set (sum2 := add64 s2a p42).
  set (s3a := add64 p14 p23).
  set (s4a := add64 p31 p13).
  set (c1 := ltu64 sum1 p34).
  set (c2b := ltu64 sum2 s2a).
  set (c3a := ltu64 s3a p14).
  set (s3b := add64 s3a p41).
  set (sum5 := add64 p12 p21).
  set (sum1Shr32 := shr64 sum1 32).
  set (sum1Shl32 := shl64 sum1 32).
  set (c4a := ltu64 s4a p31).
  set (sum4 := add64 s4a p22).
  set (sum2Hi := add64 c2a c2b).
  set (c3b := ltu64 s3b s3a).
  set (sum3 := add64 s3b p32).
  set (c5 := ltu64 sum5 p12).
  set (c1Shl32 := shl64 c1 32).
  set (lo_lo := add64 sum1Shl32 p44).
  set (sum5Shr32 := shr64 sum5 32).
  set (sum5Shl32 := shl64 sum5 32).
  set (c4b := ltu64 sum4 s4a).
  set (hh1 := add64 c4a p11).
  set (c3ab := add64 c3a c3b).
  set (c3c := ltu64 sum3 s3b).
  set (r0c := ltu64 lo_lo sum1Shl32).
  set (sum1Mid := Z.lor sum1Shr32 c1Shl32).
  set (sum3Shr32 := shr64 sum3 32).
  set (sum3Shl32 := shl64 sum3 32).
  set (c5Shl32 := shl64 c5 32).
  set (hh2 := add64 hh1 c4b).
  set (m1 := add64 sum4 sum2Hi).
  set (sum3Hi := add64 c3ab c3c).
  set (r1a := add64 sum2 sum1Mid).
  set (sum5MidHi := Z.lor c5Shl32 sum5Shr32).
  set (cm1 := ltu64 m1 sum4).
  set (m2 := add64 m1 sum5Shl32).
  set (cr1a := ltu64 r1a sum2).
  set (sum3HiShl32 := shl64 sum3Hi 32).
  set (r1 := add64 r1a sum3Shl32).
  set (hh3 := add64 hh2 cm1).
  set (cm2 := ltu64 m2 m1).
  set (cr1b := ltu64 r1 r1a).
  set (lo_hi := add64 r1 r0c).
  set (sum3Mid := Z.lor sum3Shr32 sum3HiShl32).
  set (hh4 := add64 hh3 sum5MidHi).
  set (r1Hi := add64 cr1a cr1b).
  set (carry := ltu64 lo_hi r1).
  set (hh5 := add64 hh4 cm2).
  set (m3 := add64 m2 sum3Mid).
  set (cm3 := ltu64 m3 m2).
  set (m4 := add64 m3 r1Hi).
  set (hh6 := add64 hh5 cm3).
  set (cm4 := ltu64 m4 m3).
  set (hi_lo := add64 m4 carry).
  set (hh7 := add64 hh6 cm4).
  set (cm5 := ltu64 hi_lo m4).
  set (hi_hi := add64 hh7 cm5).
  cbv beta iota.

  pose proof (Z.div_mod aSigHi (2^32) ltac:(lia)) as DMa1. pose proof (Z.mod_pos_bound aSigHi (2^32) ltac:(lia)) as MBa1.
  pose proof (Z.div_mod aSigLo (2^32) ltac:(lia)) as DMa2. pose proof (Z.mod_pos_bound aSigLo (2^32) ltac:(lia)) as MBa2.
  pose proof (Z.div_mod bSigHi (2^17) ltac:(lia)) as DMb1. pose proof (Z.mod_pos_bound bSigHi (2^17) ltac:(lia)) as MBb1.
  pose proof (Z.div_mod bSigLo (2^49) ltac:(lia)) as DMb2. pose proof (Z.mod_pos_bound bSigLo (2^49) ltac:(lia)) as MBb2.
  assert (HA1 : A1 = aSigHi / 2^32 + 2^16 /\ 0 <= aSigHi / 2^32 < 2^16).
  { assert (0 <= aSigHi / 2^32 < 2^16) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    split; [|lia]. cbv delta [A1]; nobodies. rewrite shiftr_div by lia. change 0x10000 with (1 * 2^16). rewrite lor_low_high; lia. }
  clearbody A1.
  assert (HA2 : A2 = aSigHi mod 2^32) by (cbv delta [A2]; apply zext32_val). clearbody A2.
  assert (HA3 : A3 = aSigLo / 2^32 /\ 0 <= aSigLo / 2^32 < 2^32).
  { split; [cbv delta [A3]; apply shiftr_div; lia|]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  clearbody A3.
  assert (HA4 : A4 = aSigLo mod 2^32) by (cbv delta [A4]; apply zext32_val). clearbody A4.
  assert (HbHi15 : bHi15 = bSigHi * 2^15 + bSigLo / 2^49 /\ 0 <= bSigLo / 2^49 < 2^15).
  { assert (0 <= bSigLo / 2^49 < 2^15) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    split; [|lia]. cbv delta [bHi15]; nobodies. rewrite shiftr_div by lia. rewrite (shl64_small bSigHi 15) by lia.
    rewrite lor_low_high; lia. }
  clearbody bHi15.
  assert (HB1 : B1 = bSigHi / 2^17 + 2^31 /\ 0 <= bSigHi / 2^17 < 2^31).
  { assert (0 <= bSigHi / 2^17 < 2^31) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    split; [|lia]. cbv delta [B1]; nobodies. rewrite (shl64_small bSigHi 15), shiftr_div by lia.
    replace (bSigHi * 2^15 / 2^32) with (bSigHi / 2^17).
    2:{ symmetry. rewrite <- (Z.div_div _ (2^15) (2^17)) by lia. f_equal. rewrite Z.div_mul; lia. }
    change 0x80000000 with (1 * 2^31). rewrite lor_low_high; lia. }
  clearbody B1.
  assert (HB2 : B2 = (bSigHi mod 2^17) * 2^15 + bSigLo / 2^49).
  { cbv delta [B2]; nobodies. rewrite zext32_val. destruct HbHi15 as [-> _]. symmetry. apply Z.mod_unique with (q := bSigHi / 2^17); [lia|]. nia. }
  clearbody B2.
  assert (HbLo15 : bLo15 = (bSigLo mod 2^49) * 2^15).
  { cbv delta [bLo15]; nobodies. rewrite shl64_val by lia. symmetry. apply Z.mod_unique with (q := bSigLo / 2^49); [lia|nia]. }
  clearbody bLo15.
  assert (HB3 : B3 = bLo15 / 2^32 /\ 0 <= bLo15 / 2^32 < 2^32).
  { split; [cbv delta [B3]; apply shiftr_div; lia|]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  clearbody B3.
  assert (HB4 : B4 = bLo15 mod 2^32) by (cbv delta [B4]; apply zext32_val). clearbody B4.
  pose proof (Z.div_mod bLo15 (2^32) ltac:(lia)) as DMb3. pose proof (Z.mod_pos_bound bLo15 (2^32) ltac:(lia)) as MBb3.

  set (qa1 := aSigHi / 2^32) in *; set (ra1 := aSigHi mod 2^32) in *;
  set (qa2 := aSigLo / 2^32) in *; set (ra2 := aSigLo mod 2^32) in *;
  set (qb1 := bSigHi / 2^17) in *; set (rb1 := bSigHi mod 2^17) in *;
  set (qb2 := bSigLo / 2^49) in *; set (rb2 := bSigLo mod 2^49) in *;
  set (qb3 := bLo15 / 2^32) in *; set (rb3 := bLo15 mod 2^32) in *;
  clearbody qa1 ra1 qa2 ra2 qb1 rb1 qb2 rb2 qb3 rb3.

  fact_mul p13. fact_mul p23. fact_mul p24. fact_mul p33. fact_mul p43. fact_mul p44. fact_mul p11. fact_mul p14.
  fact_mul p21. fact_mul p22. fact_mul p41. fact_mul p31. fact_mul p34. fact_mul p42. fact_mul p12. fact_mul p32.
  assert (B11 : p11 < 2^32 * 2^17) by (destruct Mp11 as [E]; rewrite E; clear -HA1 HB1; apply Z.mul_lt_mono_nonneg; lia).
  fact_addc s2a c2a. fact_addc sum1 c1. fact_addc sum2 c2b. fact_addc s3a c3a. fact_addc s4a c4a.
  fact_addc s3b c3b. fact_addc sum5 c5.
  fact_shr sum1Shr32. fact_shl32 sum1Shl32 sum1Shr32.
  fact_addc sum4 c4b. fact_adds sum2Hi. fact_addc sum3 c3c.
  fact_shl_small c1Shl32.
  fact_addc lo_lo r0c.
  fact_shr sum5Shr32. fact_shl32 sum5Shl32 sum5Shr32.
  fact_adds hh1. fact_adds c3ab.
  assert (HsM : sum1Mid = sum1Shr32 + c1 * 2^32).
  { cbv delta [sum1Mid]; nobodies. rewrite Lc1Shl32. rewrite lor_low_high; lia. }
  clearbody sum1Mid.
  fact_shr sum3Shr32. fact_shl32 sum3Shl32 sum3Shr32.
  fact_shl_small c5Shl32.
  fact_adds hh2. fact_addc m1 cm1. fact_adds sum3Hi. fact_addc r1a cr1a.
  assert (Hs5M : sum5MidHi = c5 * 2^32 + sum5Shr32).
  { cbv delta [sum5MidHi]; nobodies. rewrite Lc5Shl32. rewrite lor_high_low; lia. }
  clearbody sum5MidHi.
  fact_addc m2 cm2.
  fact_shl_small sum3HiShl32.
  fact_addc r1 cr1b. fact_adds hh3. fact_addc lo_hi carry.
  assert (Hs3M : sum3Mid = sum3Shr32 + sum3Hi * 2^32).
  { cbv delta [sum3Mid]; nobodies. rewrite Lsum3HiShl32. rewrite lor_low_high; lia. }
  clearbody sum3Mid.
  fact_adds hh4. fact_adds r1Hi. fact_adds hh5. fact_addc m3 cm3. fact_addc m4 cm4. fact_adds hh6.
  fact_addc hi_lo cm5. fact_adds hh7. fact_adds hi_hi.
  assert (NET : hi_hi * 2^192 + hi_lo * 2^128 + lo_hi * 2^64 + lo_lo =
    p44 + 2^32 * (p34 + p43) + 2^64 * (p24 + p33 + p42) + 2^96 * (p14 + p23 + p41 + p32)
    + 2^128 * (p31 + p13 + p22) + 2^160 * (p12 + p21) + 2^192 * p11) by lia.
  assert (R4 : 0 <= hi_hi < 2 ^ 64 /\ 0 <= hi_lo < 2 ^ 64 /\ 0 <= lo_hi < 2 ^ 64 /\ 0 <= lo_lo < 2 ^ 64) by lia.
  destruct R4 as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  rewrite NET.
  destruct Mp13 as [->]. destruct Mp23 as [->]. destruct Mp24 as [->]. destruct Mp33 as [->].
  destruct Mp43 as [->]. destruct Mp44 as [->]. destruct Mp11 as [->]. destruct Mp14 as [->].
  destruct Mp21 as [->]. destruct Mp22 as [->]. destruct Mp41 as [->]. destruct Mp31 as [->].
  destruct Mp34 as [->]. destruct Mp42 as [->]. destruct Mp12 as [->]. destruct Mp32 as [->].
  transitivity ((A1 * 2^96 + A2 * 2^64 + A3 * 2^32 + A4) * (B1 * 2^96 + B2 * 2^64 + B3 * 2^32 + B4)); [ring|].
  replace (A1 * 2^96 + A2 * 2^64 + A3 * 2^32 + A4) with (2 ^ 112 + aSigHi * 2 ^ 64 + aSigLo) by lia.
  replace (B1 * 2^96 + B2 * 2^64 + B3 * 2^32 + B4) with ((2 ^ 112 + bSigHi * 2 ^ 64 + bSigLo) * 2 ^ 15) by lia.
  reflexivity.
Qed.

Lemma mul_round_exact : forall signHi resHi resLo,
  mul_round signHi resHi resLo 0 0 = mk128 (Z.lor resHi signHi) resLo.
Proof. intros. reflexivity. Qed.

Lemma mul_finish_exact : forall signHi pe hh hl, 1 <= pe ->
  mul_finish signHi pe hh hl 0 0 = mul_round signHi (Z.lor (shl64 (wrap64 pe) 48) (Z.land hh MASK48)) hl 0 0.
Proof.
  intros signHi pe hh hl Hpe. unfold mul_finish.
  replace (pe <=? 0) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

Lemma words_of_aligned : forall hh hl lh ll M,
  0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 -> 0 <= M ->
  hh * 2^192 + hl * 2^128 + lh * 2^64 + ll = M * 2^128 ->
  ll = 0 /\ lh = 0 /\ hh * 2^64 + hl = M.
Proof.
  intros hh hl lh ll M Hhh Hhl Hlh Hll HM E.
  assert (ll = 0) by lia. subst ll.
  assert (lh = 0) by lia. subst lh. lia.
Qed.

Lemma shl1_words : forall hh hl lh ll,
  0 <= hh < 2^63 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  let hh1 := Z.lor (shl64 hh 1) (Z.shiftr hl 63) in
  let hl1 := Z.lor (shl64 hl 1) (Z.shiftr lh 63) in
  let lh1 := Z.lor (shl64 lh 1) (Z.shiftr ll 63) in
  let ll1 := shl64 ll 1 in
  0 <= hh1 < 2^64 /\ 0 <= hl1 < 2^64 /\ 0 <= lh1 < 2^64 /\ 0 <= ll1 < 2^64 /\
  hh1 * 2^192 + hl1 * 2^128 + lh1 * 2^64 + ll1 = 2 * (hh * 2^192 + hl * 2^128 + lh * 2^64 + ll).
Proof.
  intros hh hl lh ll Hhh Hhl Hlh Hll. cbv zeta.
  assert (SH : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
     Z.lor (shl64 x 1) (Z.shiftr y 63) = (2 * x) mod 2^64 + y / 2^63 /\ 0 <= y / 2^63 <= 1 /\ (2 * x) mod 2^64 = 2 * x - 2^64 * (x / 2^63)).
  { intros x y Hx Hy. rewrite shl64_val, shiftr_div by lia. change (2^1) with 2.
    assert (Hq : 0 <= y / 2^63 <= 1) by dlia.
    assert (Hm : (2 * x) mod 2 ^ 64 = 2 * x - 2^64 * (x / 2^63)) by dlia.
    split; [|split; [exact Hq| exact Hm]].
    rewrite Z.mul_comm. rewrite Hm.
    replace (2 * x - 2 ^ 64 * (x / 2 ^ 63)) with ((x - 2^63 * (x / 2^63)) * 2^1) by lia.
    rewrite lor_high_low; try lia; dlia. }
  destruct (SH hh hl) as (E1 & Q1 & M1); [lia|lia|].
  destruct (SH hl lh) as (E2 & Q2 & M2); [lia|lia|].
  destruct (SH lh ll) as (E3 & Q3 & M3); [lia|lia|].
  rewrite E1, E2, E3. rewrite shl64_val by lia. change (2^1) with 2.
  assert (M4 : (ll * 2) mod 2^64 = 2 * ll - 2^64 * (ll / 2^63)) by dlia.
  rewrite M4.
  assert (hh / 2^63 = 0) by (apply Z.div_small; lia).
  pose proof (Z.mod_pos_bound (2 * hl) (2^64) ltac:(lia)). pose proof (Z.mod_pos_bound (2 * lh) (2^64) ltac:(lia)).
  dlia.
Qed.

Lemma mulc_p4_exact : forall s aExp bExp scale hh hl lh ll M k,
  0 <= s <= 1 -> (k = 0 \/ k = 1) -> 2^112 <= M < 2^113 ->
  0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  hh * 2^192 + hl * 2^128 + lh * 2^64 + ll = M * 2^(127 + k) ->
  0 <= aExp -> 0 <= bExp -> aExp + bExp < 2^63 ->
  1 <= aExp + bExp + scale - 16383 + k <= 32766 ->
  mulc_p4 (s * 2^63) aExp bExp scale (hh, hl, lh, ll) = f128_pack s (aExp + bExp + scale - 16383 + k) (M - 2^112).
Proof.
  intros s aExp bExp scale hh hl lh ll M k Hs Hk HM Hhh Hhl Hlh Hll E HaE HbE Hsum Hpe.
  pose proof (Z.div_mod M (2^64) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound M (2^64) ltac:(lia)) as MB.
  assert (QM : 2^48 <= M / 2^64 < 2^49) by dlia.
  set (q := M / 2^64) in *. set (r := M mod 2^64) in *. clearbody q r.
  unfold mulc_p4. rewrite add64_small by lia. change 0x3fff with 16383. change 0x7fff with 32767.
  assert (FIN : forall pe hh' hl', 1 <= pe <= 32766 -> hh' = q -> hl' = r ->
     mul_finish (s * 2^63) pe hh' hl' 0 0 = f128_pack s pe (M - 2^112)).
  { intros pe hh' hl' Hpe' -> ->. rewrite mul_finish_exact, mul_round_exact by lia.
    rewrite wrap64_id by lia. rewrite (shl64_small pe 48) by lia. rewrite land_mask48.
    replace (q mod 2^48) with (q - 2^48) by (apply Z.mod_unique with (q := 1); lia).
    rewrite (lor_high_low pe (q - 2^48) 48) by lia.
    rewrite lor_low_high by lia. rewrite mk128_val by lia. unfold f128_pack. lia. }
  destruct Hk as [-> | ->].
  -
    rewrite Z.add_0_r in *.
    assert (Hhh63 : hh < 2^48) by lia.
    rewrite (shl64_small hh 15) by lia. rewrite is_neg64_val by lia.
    replace (2 ^ 63 <=? hh * 2 ^ 15) with false by (symmetry; apply Z.leb_gt; lia).
    destruct (shl1_words hh hl lh ll) as (R1 & R2 & R3 & R4 & E2); [lia|lia|lia|lia|].
    cbv zeta.
    set (hh1 := Z.lor (shl64 hh 1) (Z.shiftr hl 63)) in *.
    set (hl1 := Z.lor (shl64 hl 1) (Z.shiftr lh 63)) in *.
    set (lh1 := Z.lor (shl64 lh 1) (Z.shiftr ll 63)) in *.
    set (ll1 := shl64 ll 1) in *. clearbody hh1 hl1 lh1 ll1.
    rewrite E in E2. change (2^(127+0)) with (2^127) in E2.
    replace (2 * (M * 2^127)) with (M * 2^128) in E2 by lia.
    destruct (words_of_aligned hh1 hl1 lh1 ll1 M) as (-> & -> & W); try lia.
    replace (32767 <=? aExp + bExp + (scale - 16383)) with false by (symmetry; apply Z.leb_gt; lia).
    replace (aExp + bExp + (scale - 16383)) with (aExp + bExp + scale - 16383) by lia.
    apply FIN; lia.
  -
    change (2^(127+1)) with (2^128) in E.
    destruct (words_of_aligned hh hl lh ll M) as (-> & -> & W); try lia.
    assert (hh = q) by lia.
    rewrite (shl64_small hh 15) by lia. rewrite is_neg64_val by lia.
    replace (2 ^ 63 <=? hh * 2 ^ 15) with true by (symmetry; apply Z.leb_le; lia).
    replace (aExp + bExp + (scale - 16383) + 1 <? 32767) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    replace (aExp + bExp + (scale - 16383) + 1) with (aExp + bExp + scale - 16383 + 1) by lia.
    apply FIN; lia.
Qed.

Lemma xorbit01 : forall sa sb, 0 <= sa <= 1 -> 0 <= sb <= 1 -> 0 <= Z.lxor sb sa <= 1.
Proof.
  intros sa sb Ha Hb.
  assert (Da : sa = 0 \/ sa = 1) by lia. assert (Db : sb = 0 \/ sb = 1) by lia.
  destruct Da as [-> | ->]; destruct Db as [-> | ->]; cbn; lia.
Qed.

Theorem f128_mul_exact : forall sa Ea Ta sb Eb Tb M k,
  packed sa Ea Ta -> packed sb Eb Tb -> 1 <= Ea <= 32766 -> 1 <= Eb <= 32766 ->
  (k = 0 \/ k = 1) -> 2^112 <= M < 2^113 ->
  (2^112 + Ta) * (2^112 + Tb) = M * 2^(112 + k) ->
  1 <= Ea + Eb - 16383 + k <= 32766 ->
  f128_mul (f128_pack sa Ea Ta) (f128_pack sb Eb Tb) = f128_pack (Z.lxor sb sa) (Ea + Eb - 16383 + k) (M - 2^112).
Proof.
  intros sa Ea Ta sb Eb Tb M k PA PB HEa HEb Hk HM PROD Hpe.
  destruct PA as [Hsa HEa' HTa]. destruct PB as [Hsb HEb' HTb].
  pose proof (T_split Ta HTa) as (Htha & Htla & ETa). pose proof (T_split Tb HTb) as (Hthb & Htlb & ETb).
  unfold f128_mul.
  rewrite !f128_pack_hi, !f128_pack_lo by (constructor; lia).
  rewrite !hiword_exp by lia.
  rewrite !add64_val. change 0xffffffffffff8001 with (2^64 - 32767). change 0xffffffffffff8002 with (2^64 - 32766).
  rewrite !Z.mod_small by lia.
  replace (Ea + (2 ^ 64 - 32767) <? 2 ^ 64 - 32766) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Eb + (2 ^ 64 - 32767) <=? 2 ^ 64 - 32767) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [orb negb].
  rewrite Z.shiftr_lxor, !hiword_sign by lia.
  pose proof (xorbit01 sa sb Hsa Hsb) as Hx.
  rewrite (shl64_small (Z.lxor sb sa) 63) by lia.
  rewrite !hiword_frac by lia.
  rewrite mul_core_restage.
  pose proof (mulc_net_val (Ta / 2^64) (Ta mod 2^64) (Tb / 2^64) (Tb mod 2^64) Htha Htla Hthb Htlb) as NV.
  destruct (mulc_net (Ta / 2^64) (Ta mod 2^64) (Tb / 2^64) (Tb mod 2^64)) as [[[hh hl] lh] ll].
  destruct NV as (R1 & R2 & R3 & R4 & E).
  replace (2 ^ 112 + Ta / 2 ^ 64 * 2 ^ 64 + Ta mod 2 ^ 64) with (2^112 + Ta) in E by lia.
  replace (2 ^ 112 + Tb / 2 ^ 64 * 2 ^ 64 + Tb mod 2 ^ 64) with (2^112 + Tb) in E by lia.
  replace (Ea + Eb - 16383 + k) with (Ea + Eb + 0 - 16383 + k) by lia.
  apply mulc_p4_exact; try lia.
  rewrite E. rewrite Z.mul_assoc, PROD. rewrite (pow2_split 127 k), (pow2_split 112 k) by lia.
  change (2^127) with (2^112 * 2^15). lia.
Qed.

Theorem f128_mul_zero : forall sa Ea Ta sb Eb Tb,
  packed sa Ea Ta -> packed sb Eb Tb -> Ea <= 32766 -> Eb <= 32766 ->
  ((Ea = 0 /\ Ta = 0) \/ (Eb = 0 /\ Tb = 0)) ->
  (Ea = 0 -> Ta = 0) -> (Eb = 0 -> Tb = 0) ->
  f128_mul (f128_pack sa Ea Ta) (f128_pack sb Eb Tb) = f128_pack (Z.lxor sb sa) 0 0.
Proof.
  intros sa Ea Ta sb Eb Tb PA PB HEa HEb Hz Ha0 Hb0.
  destruct PA as [Hsa HEa' HTa]. destruct PB as [Hsb HEb' HTb].
  pose proof (T_split Ta HTa) as (Htha & Htla & ETa). pose proof (T_split Tb HTb) as (Hthb & Htlb & ETb).
  unfold f128_mul.
  rewrite !f128_pack_hi, !f128_pack_lo by (constructor; lia).
  rewrite !hiword_exp by lia.
  rewrite !add64_val. change 0xffffffffffff8001 with (2^64 - 32767). change 0xffffffffffff8002 with (2^64 - 32766).
  rewrite !Z.mod_small by lia.
  rewrite Z.shiftr_lxor, !hiword_sign by lia.
  pose proof (xorbit01 sa sb Hsa Hsb) as Hx.
  rewrite (shl64_small (Z.lxor sb sa) 63) by lia.
  rewrite !hiword_abs by lia. rewrite inf_hi_eq.
  assert (CASE : (Ea + (2 ^ 64 - 32767) <? 2 ^ 64 - 32766) || (Eb + (2 ^ 64 - 32767) <=? 2 ^ 64 - 32767) = true).
  { destruct Hz as [[-> _]|[-> _]].
    - replace (0 + (2 ^ 64 - 32767) <? 2 ^ 64 - 32766) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - replace (0 + (2 ^ 64 - 32767) <=? 2 ^ 64 - 32767) with true by (symmetry; apply Z.leb_le; lia). apply Bool.orb_true_r. }
  rewrite CASE. cbn [negb].
  replace (Ea * 2 ^ 48 + Ta / 2 ^ 64 =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Ea * 2 ^ 48 + Ta / 2 ^ 64 <? 32767 * 2 ^ 48) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (Eb * 2 ^ 48 + Tb / 2 ^ 64 =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Eb * 2 ^ 48 + Tb / 2 ^ 64 <? 32767 * 2 ^ 48) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb].
  rewrite !lor_eqb0 by (try apply Z.lxor_nonneg; lia).
  rewrite !lxor_eqb0.
  replace (Ea * 2 ^ 48 + Ta / 2 ^ 64 =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Eb * 2 ^ 48 + Tb / 2 ^ 64 =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [andb].
  assert (MK : mk128 (Z.lxor sb sa * 2 ^ 63) 0 = f128_pack (Z.lxor sb sa) 0 0).
  { rewrite mk128_val by lia. unfold f128_pack. lia. }
  destruct Hz as [[-> ->]|[-> ->]].
  - change (0 mod 2^64 =? 0) with true. change (0 * 2^48 + 0 / 2^64 =? 0) with true. cbn [andb]. exact MK.
  - change (0 mod 2^64 =? 0) with true. change (0 * 2^48 + 0 / 2^64 =? 0) with true. cbn [andb].
    destruct ((Ta mod 2 ^ 64 =? 0) && (Ea * 2 ^ 48 + Ta / 2 ^ 64 =? 0)); exact MK.
Qed.
