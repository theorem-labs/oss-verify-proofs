(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require Bool.
From Stdlib Require List.
From Stdlib Require Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require SoftFloat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require SoftFloatProps.
From LinuxProcessSemantics.Riscv Require Fpu.
Module SF_Class.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.Prelim OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.SoftFloat OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.SoftFloatProps.
Import LinuxProcessSemantics.Riscv.Fpu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Definition nn128 (E T : Z) : Prop := E = 32767 -> T = 0.       (* [comment removed for export] *)
Definition fin128 (E : Z) : Prop := E <= 32766.                 (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fp_is_nan_double_fields : forall sd Ed Td, 0 <= sd <= 1 -> 0 <= Ed <= 2047 -> 0 <= Td < 2^52 ->
  (Ed = 2047 -> Td = 0) ->
  fp_is_nan fmt_double (sd * 2^63 + Ed * 2^52 + Td) = false.
Proof.
  intros sd Ed Td Hs HE HT HN. unfold fp_is_nan, fp_exp_field, fp_man_field.
  replace (fp_mw fmt_double) with 52 by reflexivity.
  replace (fp_ew fmt_double) with 11 by reflexivity.
  change (Z.ones 11) with (2^11 - 1). change (Z.ones 52) with (2^52 - 1).
  rewrite !land_ones_mod, shiftr_div by lia.
  replace (((sd * 2 ^ 63 + Ed * 2 ^ 52 + Td) / 2 ^ 52) mod 2^11) with Ed by dlia.
  replace ((sd * 2 ^ 63 + Ed * 2 ^ 52 + Td) mod 2^52) with Td by dlia.
  destruct (Z.eqb_spec Ed (2^11-1)) as [E|E]; [| reflexivity].
  rewrite (HN E). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shr_bound : forall x k n, 0 <= x < 2^(n+k) -> 0 <= k -> 0 <= n -> 0 <= Z.shiftr x k < 2^n.
Proof.
  intros x k n Hx Hk Hn. rewrite shiftr_div by lia. rewrite Z.pow_add_r in Hx by lia.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma shr_bound64 : forall x k, 0 <= x < 2^64 -> 0 <= k -> 0 <= Z.shiftr x k < 2^64.
Proof.
  intros x k Hx Hk. rewrite shiftr_div by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. pose proof (pow2_ge1 k Hk). nia.
Qed.

Lemma shl64_range : forall x n, 0 <= n -> 0 <= shl64 x n < 2^64.
Proof. intros. rewrite shl64_val by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma trunc_round_cases : forall x rb, 0 <= x -> x + 1 < 2^64 ->
  trunc_round x rb = x \/ trunc_round x rb = x + 1.
Proof.
  intros x rb Hx Hx1. unfold trunc_round.
  destruct (negb (rb <? HALF60 + 1)).
  - right. apply add64_small. lia.
  - destruct (negb (negb (rb =? HALF60))); [| left; reflexivity].
    change (Z.land x 1) with (Z.land x (2^1 - 1)). rewrite land_ones_mod by lia.
    rewrite add64_small by dlia. dlia.
Qed.

(* [comment removed for export] *)
Lemma pack_double : forall s de fr, 0 <= s <= 1 -> 0 <= de <= 2047 -> 0 <= fr < 2^52 ->
  Z.lor (Z.lor (shl64 de 52) (shl64 s 63)) fr = s * 2^63 + de * 2^52 + fr.
Proof.
  intros s de fr Hs Hde Hfr.
  rewrite (shl64_small de 52) by lia. rewrite (shl64_small s 63) by lia.
  replace (s * 2^63) with ((s * 2^11) * 2^52) by lia.
  assert (L1 : Z.lor (de * 2^52) (s * 2^11 * 2^52) = (s * 2^11 + de) * 2^52).
  { rewrite <- Z.shiftl_mul_pow2, <- Z.shiftl_mul_pow2, <- Z.shiftl_lor, Z.shiftl_mul_pow2 by lia.
    f_equal. destruct (Z.eq_dec s 0) as [->|]; [rewrite Z.mul_0_l, Z.lor_0_r; lia|].
    replace s with 1 by lia. change (1 * 2^11) with (1 * 2^11 + 0) at 1.
    rewrite Z.lor_comm. rewrite <- (lor_high_low 1 de 11) by lia. f_equal. }
  rewrite L1. rewrite lor_high_low by lia. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition t2d_pair (E th tl : Z) : Z * Z :=
  let srcExp := E in
  let sigHi := th in
  let a_lo := tl in
  let candM1 := add64 srcExp 0xffffffffffffc3ff in
    if negb (2045 <? candM1) then
      let sig0 := Z.lor (Z.shiftr a_lo 60) (shl64 sigHi 4) in
      let roundBits := Z.shiftr (shl64 a_lo 4) 4 in
      let exp0 := add64 candM1 1 in
      let sig1 := trunc_round sig0 roundBits in
      let carry := Z.shiftr sig1 52 in
      let dstSigFrac := Z.land (sub64 carry 1) sig1 in
      let dstExp := add64 carry exp0 in
      (dstExp, dstSigFrac)
    else
      let isNaN := if Z.lor a_lo sigHi =? 0 then false
                   else negb (negb (srcExp =? 0x7fff)) in
      if isNaN then
        let dstSigFrac := Z.lor (Z.lor (Z.shiftr a_lo 60) DQUIET) (shl64 sigHi 4) in
        let dstExp := 2047 in
        (dstExp, dstSigFrac)
      else if negb (srcExp <=? 0x43fe) then
        let dstSigFrac := 0 in
        let dstExp := 2047 in
        (dstExp, dstSigFrac)
      else
        let expZ := eqz64 srcExp in
        let k := Z.lxor expZ 0x3c01 in
        let shift := sub64 k srcExp in
        if lt_s64 112 shift then (0, 0)
        else
          let expNZ := nez64 srcExp in
          let shNZ0 := Z.lxor k srcExp in
          let negsh := sext32 (sub64 0 shift) in
          let implicit := shl64 expNZ 48 in
          let shNZ := nez64 shNZ0 in
          let nW := sext32 (sub64 128 shift) in
          let t0 := shl64 a_lo (Z.land negsh 63) in
          let sigHi1 := Z.lor sigHi implicit in
          let n := zext32 nW in
          let nM64 := sub64 n 64 in
          let slLo := Z.land (sra63 nM64) t0 in
          let slHi := if negb (is_neg64 nM64) then shl64 a_lo (Z.land n 63)
                      else Z.lor (shl64 sigHi1 (Z.land negsh 63))
                                 (Z.shiftr (Z.shiftr a_lo 1) (Z.land (not64 n) 63)) in
          let stickySrc := Z.lor slLo slHi in
          let m := zext32 shift in
          let sticky0 := nez64 stickySrc in
          let mM64 := sub64 m 64 in
          let sticky := Z.land shNZ sticky0 in
          let srLo := if negb (is_neg64 mM64) then Z.shiftr sigHi1 (Z.land m 63)
                      else Z.lor (Z.shiftr a_lo (Z.land shift 63))
                                 (shl64 (shl64 sigHi1 1) (Z.land (not64 m) 63)) in
          let srHi0 := Z.shiftr sigHi1 (Z.land shift 63) in
          let srHi := Z.land (sra63 mM64) srHi0 in
          let sig0 := Z.lor (Z.shiftr srLo 60) (shl64 srHi 4) in
          let roundBits := Z.lor (Z.shiftr (shl64 srLo 4) 4) sticky in
          let sig1 := trunc_round sig0 roundBits in
          let carry := nez64 (Z.shiftr sig1 52) in
          let dstSigFrac := Z.lxor sig1 (shl64 carry 52) in
          let dstExp := carry in
          (dstExp, dstSigFrac).

Lemma f128_to_d_restage : forall s E T, packed s E T ->
  f128_to_d (f128_pack s E T) =
    let p := t2d_pair E (T / 2^64) (T mod 2^64) in Z.lor (Z.lor (shl64 (fst p) 52) (shl64 s 63)) (snd p).
Proof.
  intros s E T PK. pose proof PK as [Hs HE HT]. pose proof (T_split T HT) as (Hth & Htl & ET).
  unfold f128_to_d, t2d_pair.
  rewrite (f128_pack_hi s E T PK), (f128_pack_lo s E T PK).
  rewrite hiword_exp, hiword_frac16, hiword_sign by lia.
  cbv zeta. repeat match goal with |- context [let '(_, _) := ?P in _] => destruct P end. reflexivity.
Qed.

Lemma t2d_pair_ok : forall E T, 0 <= E <= 32767 -> 0 <= T < 2^112 -> nn128 E T ->
  let p := t2d_pair E (T / 2^64) (T mod 2^64) in
  0 <= fst p <= 2047 /\ 0 <= snd p < 2^52 /\ (fst p = 2047 -> snd p = 0).
Proof.
  intros E T HE HT NN. pose proof (T_split T HT) as (Hth & Htl & ET).
  set (th := T / 2^64) in *. set (tl := T mod 2^64) in *.
  unfold t2d_pair. cbv zeta.
  set (c1 := add64 E 0xffffffffffffc3ff).
  assert (C1 : c1 = if 15361 <=? E then E - 15361 else E + (2^64 - 15361)).
  { subst c1. rewrite add64_val. change 0xffffffffffffc3ff with (2^64 - 15361).
    destruct (Z.leb_spec 15361 E).
    - replace (E + (2^64 - 15361)) with ((E - 15361) + 1 * 2^64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
    - apply Z.mod_small. lia. }
  destruct (Z.ltb_spec 2045 c1) as [GT|LE]; cbn [negb].
  2:{ (* [comment removed for export] *)
    assert (HE2 : 15361 <= E <= 17406) by (destruct (Z.leb_spec 15361 E); lia).
    replace (15361 <=? E) with true in C1 by (symmetry; apply Z.leb_le; lia).
    set (sig0 := Z.lor (Z.shiftr tl 60) (shl64 th 4)).
    assert (S0 : 0 <= sig0 < 2^52).
    { subst sig0. rewrite (shl64_small th 4) by lia. apply lor_bound; [lia| |lia].
      rewrite shiftr_div by lia. dlia. }
    set (sig1 := trunc_round sig0 (Z.shiftr (shl64 tl 4) 4)).
    assert (S1 : sig1 = sig0 \/ sig1 = sig0 + 1) by (apply trunc_round_cases; lia).
    cbn [fst snd].
    rewrite shiftr_div by lia.
    destruct (Z.eq_dec sig1 (2^52)) as [EQ|NE].
    - rewrite EQ. change (2^52 / 2^52) with 1. rewrite (sub64_small 1 1) by lia. rewrite Z.land_0_l.
      rewrite add64_val, C1, add64_val.
      rewrite (Z.mod_small (E - 15361 + 1)) by lia. rewrite Z.mod_small by lia. lia.
    - assert (S1' : 0 <= sig1 < 2^52) by lia.
      rewrite (Z.div_small sig1) by lia. rewrite sub64_val. change ((0 - 1) mod 2^64) with (2^64 - 1).
      rewrite Z.land_comm, land_ones_mod, (Z.mod_small sig1) by lia.
      rewrite !add64_val, C1. rewrite (Z.mod_small (E - 15361 + 1)) by lia. rewrite Z.mod_small by lia. lia. }
  (* [comment removed for export] *)
  assert (HE2 : E < 15361 \/ 17406 < E) by (destruct (Z.leb_spec 15361 E); lia).
  match goal with |- context [if (if ?c then false else ?d) then _ else _] =>
    replace (if c then false else d) with false end.
  2:{ destruct (Z.eqb_spec (Z.lor tl th) 0) as [|NZ]; [reflexivity|].
      destruct (Z.eqb_spec E 0x7fff) as [E7|]; [| reflexivity].
      exfalso. apply NZ. rewrite (NN E7) in ET.
      assert (Z1 : th = 0) by lia. assert (Z2 : tl = 0) by lia. rewrite Z1, Z2. reflexivity. }
  destruct (Z.leb_spec E 0x43fe) as [LE1|GT1]; cbn [negb].
  2:{ cbn [fst snd]. lia. }
  assert (HE3 : E < 15361) by lia. clear HE2 LE1 GT C1 c1.
  destruct (Z.eq_dec E 0) as [E0|E1].
  { rewrite E0. change (lt_s64 112 (sub64 (Z.lxor (eqz64 0) 15361) 0)) with true. cbn [fst snd]. lia. }
  replace (eqz64 E) with 0 by (unfold eqz64, b2z; replace (E =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
  change (Z.lxor 0 15361) with 15361.
  set (sh := sub64 15361 E).
  assert (SH : sh = 15361 - E) by (subst sh; apply sub64_small; lia).
  rewrite lt_s64_val by lia.
  change (2 ^ 63 <=? 112) with false.
  replace (2 ^ 63 <=? sh) with false by (symmetry; apply Z.leb_gt; lia). cbv iota.
  destruct (Z.ltb_spec 112 sh) as [BIG|SMALL]; [cbn [fst snd]; lia|].
  assert (HE4 : 15249 <= E <= 15360) by lia.
  replace (nez64 E) with 1 by (unfold nez64, b2z; replace (E =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
  rewrite (shl64_small 1 48) by lia.
  replace (Z.lor th (1 * 2^48)) with (1 * 2^48 + th) by (symmetry; apply lor_low_high; lia).
  set (sigHi1 := 1 * 2^48 + th).
  assert (SG : 2^48 <= sigHi1 < 2^49) by lia.
  rewrite (zext32_val sh), (Z.mod_small sh) by lia.
  set (srLo := if negb (is_neg64 (sub64 sh 64)) then Z.shiftr sigHi1 (Z.land sh 63)
               else Z.lor (Z.shiftr tl (Z.land sh 63)) (shl64 (shl64 sigHi1 1) (Z.land (not64 sh) 63))).
  match goal with |- context [trunc_round _ ?rb] => set (RB := rb) end.
  assert (LO : 0 <= srLo < 2^64).
  { subst srLo. destruct (negb _).
    - pose proof (shr_bound64 sigHi1 (Z.land sh 63) ltac:(lia) ltac:(apply Z.land_nonneg; lia)). lia.
    - apply lor_bound; [lia| |apply shl64_range; apply Z.land_nonneg; lia].
      apply shr_bound64; [lia|]. apply Z.land_nonneg; lia. }
  set (srHi := Z.land (sra63 (sub64 sh 64)) (Z.shiftr sigHi1 (Z.land sh 63))).
  assert (HI : 0 <= srHi < 2^48).
  { subst srHi. rewrite land63. rewrite sub64_val.
    destruct (Z.lt_ge_cases sh 64) as [L64|G64].
    - rewrite (Z.mod_small sh 64) by lia.
      replace ((sh - 64) mod 2^64) with (2^64 + sh - 64) by dlia.
      rewrite smask64_val by lia. replace (2 ^ 63 <=? 2 ^ 64 + sh - 64) with true by (symmetry; apply Z.leb_le; lia).
      rewrite ones64_eq, Z.land_comm, land_ones_mod by lia. rewrite shiftr_div by lia.
      assert (DD : sigHi1 / 2^sh <= sigHi1 / 2^1) by (apply Z.div_le_compat_l; [lia| split; [lia| apply Z.pow_le_mono_r; lia]]).
      change (2^1) with 2 in DD. pose proof (Z.div_pos sigHi1 (2^sh) ltac:(lia) ltac:(lia)).
      rewrite Z.mod_small; dlia.
    - rewrite (Z.mod_small (sh - 64)) by lia. rewrite smask64_val by lia.
      replace (2 ^ 63 <=? sh - 64) with false by (symmetry; apply Z.leb_gt; lia). rewrite Z.land_0_l. lia. }
  set (sig0 := Z.lor (Z.shiftr srLo 60) (shl64 srHi 4)).
  assert (S0 : 0 <= sig0 < 2^52).
  { subst sig0. rewrite (shl64_small srHi 4) by lia. apply lor_bound; [lia| |lia]. rewrite shiftr_div by lia. dlia. }
  set (sig1 := trunc_round sig0 RB).
  assert (S1 : sig1 = sig0 \/ sig1 = sig0 + 1) by (apply trunc_round_cases; lia).
  cbn [fst snd].
  destruct (Z.eq_dec sig1 (2^52)) as [EQ|NE].
  - rewrite EQ. change (nez64 (Z.shiftr (2 ^ 52) 52)) with 1. rewrite (shl64_small 1 52) by lia.
    change (Z.lxor (2 ^ 52) (1 * 2 ^ 52)) with 0. lia.
  - assert (S1' : 0 <= sig1 < 2^52) by lia.
    rewrite (shiftr_div sig1 52), (Z.div_small sig1) by lia. change (nez64 0) with 0. rewrite (shl64_small 0 52) by lia.
    rewrite Z.lxor_0_r. lia.
Qed.

Theorem f128_to_d_not_nan : forall s E T, packed s E T -> nn128 E T ->
  0 <= f128_to_d (f128_pack s E T) < 2^64 /\ fp_is_nan fmt_double (f128_to_d (f128_pack s E T)) = false.
Proof.
  intros s E T PK NN. pose proof PK as [Hs HE HT].
  rewrite (f128_to_d_restage s E T PK).
  pose proof (t2d_pair_ok E T HE HT NN) as OK. cbv zeta in OK |- *.
  destruct (t2d_pair E (T / 2^64) (T mod 2^64)) as [de fr]. cbn [fst snd] in OK |- *.
  destruct OK as (Hde & Hfr & HN).
  rewrite pack_double by lia. split; [lia|].
  apply fp_is_nan_double_fields; lia || exact HN.
Qed.
End SF_Class.

(* [comment removed for export] *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require SoftFloatProps2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require FmtFpDig.
Module SF_ClassMul.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.Prelim OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.SoftFloat OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.SoftFloatProps OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.SoftFloatProps2 OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.FmtFpDig.SoftFloatProps3 SF_Class.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Lemma mul_round_class : forall s resHi resLo lh ll,
  0 <= s <= 1 -> 0 <= resHi < 2^63 - 1 -> 0 <= resLo < 2^64 ->
  exists d, (d = 0 \/ d = 1) /\
    mul_round (s * 2^63) resHi resLo lh ll = s * 2^127 + (resHi * 2^64 + resLo + d).
Proof.
  intros s resHi resLo lh ll Hs Hh Hl. unfold mul_round.
  rewrite (lor_low_high s resHi 63) by lia.
  destruct (if lh =? SIGN64 then negb (ll =? 0) else is_neg64 lh).
  - exists 1. split; [lia|].
    unfold eqz64. rewrite b2z_val, !add64_val.
    destruct (Z.eq_dec resLo (2^64 - 1)) as [->|NE].
    + replace ((2 ^ 64 - 1 + 1) mod 2 ^ 64) with 0 by reflexivity. cbn [Z.eqb].
      rewrite Z.mod_small by lia. rewrite mk128_val by lia. lia.
    + rewrite (Z.mod_small (resLo + 1)) by lia.
      replace (resLo + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite Z.mod_small by lia. rewrite mk128_val by lia. lia.
  - destruct (Z.lor ll (Z.lxor lh SIGN64) =? 0).
    + change (Z.land resLo 1) with (Z.land resLo (2^1 - 1)). rewrite land_ones_mod by lia.
      pose proof (L_addc resLo (resLo mod 2^1) Hl ltac:(dlia)) as (E & R & C).
      exists (resLo mod 2^1). split; [dlia|].
      rewrite add64_val. rewrite (Z.mod_small (s * 2 ^ 63 + resHi + _)) by lia.
      rewrite mk128_val by lia. lia.
    + exists 0. split; [lia|]. rewrite mk128_val by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma pack_V : forall s V K, 0 <= s <= 1 -> 0 <= V <= K * 2^112 -> 0 <= K <= 32767 ->
  s * 2^127 + V = f128_pack s (V / 2^112) (V mod 2^112)
  /\ packed s (V / 2^112) (V mod 2^112)
  /\ V / 2^112 <= K /\ (V / 2^112 = K -> V mod 2^112 = 0).
Proof.
  intros s V K Hs HV HK. unfold f128_pack.
  split; [dlia|]. split; [constructor; dlia|]. dlia.
Qed.

Lemma wrap64_neg : forall x, -2^64 <= x < 0 -> wrap64 x = x + 2^64.
Proof. intros x Hx. unfold wrap64. rewrite ones64_eq, land_ones_mod by lia. dlia. Qed.

(* [comment removed for export] *)
Lemma mul_finish_class : forall s pe hh hl lh ll,
  0 <= s <= 1 -> -2^40 < pe < 32767 -> 0 <= hh < 2^49 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  exists E' T', mul_finish (s * 2^63) pe hh hl lh ll = f128_pack s E' T' /\ packed s E' T' /\ nn128 E' T'
    /\ E' <= Z.max pe 0 + 1 /\ (1 <= pe -> pe <= E').
Proof.
  intros s pe hh hl lh ll Hs Hpe Hhh Hhl Hlh Hll. unfold mul_finish.
  destruct (Z.leb_spec pe 0) as [LE|GT].
  - (* [comment removed for export] *)
    assert (W : wrap64 pe = if pe =? 0 then 0 else pe + 2^64).
    { destruct (Z.eqb_spec pe 0) as [->|]; [reflexivity| apply wrap64_neg; lia]. }
    assert (SH : sub64 1 (wrap64 pe) = 1 - pe).
    { rewrite W, sub64_val. destruct (Z.eqb_spec pe 0) as [->|]; [reflexivity| dlia]. }
    rewrite SH. destruct (Z.ltb_spec 127 (1 - pe)) as [BIG|SMALL].
    { exists 0, 0. rewrite mk128_val by lia. unfold f128_pack. split; [lia|]. split; [constructor; lia|]. split; [intros E; lia| lia]. }
    assert (N : add64 (wrap64 pe) 127 = pe + 127).
    { rewrite W, add64_val. destruct (Z.eqb_spec pe 0) as [->|]; [reflexivity| dlia]. }
    rewrite N. rewrite !zext32_val, (Z.mod_small (pe + 127)), (Z.mod_small (1 - pe)) by lia.
    set (sh := 1 - pe) in *.
    assert (NGsh : is_neg64 (sub64 sh 64) = (sh <? 64)).
    { rewrite sub64_val, is_neg64_val by (apply Z.mod_pos_bound; lia).
      destruct (Z.ltb_spec sh 64).
      - replace ((sh - 64) mod 2^64) with (2^64 + sh - 64) by dlia. apply Z.leb_le. lia.
      - rewrite Z.mod_small by lia. apply Z.leb_gt. lia. }
    rewrite NGsh.
    destruct (is_neg64 (sub64 (pe + 127) 64)); destruct (Z.ltb_spec sh 64) as [S64|S64]; cbv beta iota.
    all: match goal with |- context [mul_round _ ?a ?b ?c ?d] =>
      assert (HRH : 0 <= a < 2^48);
      [ | assert (HRL : 0 <= b < 2^64);
          [ | destruct (mul_round_class s a b c d) as [dd [Hdd EE]]; [lia|lia|lia|];
              rewrite EE;
              destruct (pack_V s (a * 2^64 + b + dd) 1) as (E1 & P1 & B1 & Z1); [lia|lia|lia|];
              eexists _, _; split; [exact E1|]; split; [exact P1|]; split; [intros E32; lia| split; [lia| intros; lia]] ] ]
    end.
    all: try (rewrite land63, (Z.mod_small sh 64) by lia).
    all: try lia.
    all: try (apply shr_bound64; [lia| apply Z.land_nonneg; lia]).
    all: try (apply lor_bound; [lia| apply shr_bound64; lia| apply shl64_range; apply Z.land_nonneg; lia]).
    all: rewrite shiftr_div by lia; split; [apply Z.div_pos; lia|].
    all: apply (Z.le_lt_trans _ (hh / 2^1)); [apply Z.div_le_compat_l; [lia| split; [lia| apply Z.pow_le_mono_r; lia]] | change (2^1) with 2; dlia].
  - (* [comment removed for export] *)
    rewrite wrap64_id by lia. rewrite (shl64_small pe 48) by lia. rewrite land_mask48.
    rewrite (lor_high_low pe (hh mod 2^48) 48) by (try apply Z.mod_pos_bound; lia).
    pose proof (Z.mod_pos_bound hh (2^48) ltac:(lia)) as HM.
    destruct (mul_round_class s (pe * 2^48 + hh mod 2^48) hl lh ll) as [dd [Hdd EE]]; [lia|lia|lia|].
    rewrite EE.
    destruct (pack_V s ((pe * 2^48 + hh mod 2^48) * 2^64 + hl + dd) (pe + 1)) as (E1 & P1 & B1 & Z1); [lia|lia|lia|].
    eexists _, _; split; [exact E1|]; split; [exact P1|]; split; [intros E32; apply Z1; lia| split; [lia| intros; dlia]].
Qed.

Lemma inf_pack : forall s, 0 <= s <= 1 -> mk128 (Z.lor (s * 2^63) INF_HI) 0 = f128_pack s 32767 0.
Proof.
  intros s Hs. rewrite inf_hi_eq. rewrite lor_high_low by lia. rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

Lemma zero_pack : forall s, 0 <= s <= 1 -> mk128 (s * 2^63) 0 = f128_pack s 0 0.
Proof. intros s Hs. rewrite mk128_val by lia. unfold f128_pack. lia. Qed.

(* [comment removed for export] *)
Lemma mulc_p4_class : forall s aExp bExp scale hh hl lh ll,
  0 <= s <= 1 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  2^239 <= hh * 2^192 + hl * 2^128 + lh * 2^64 + ll < 2^241 ->
  0 <= aExp -> 0 <= bExp -> aExp + bExp < 2^62 -> -2^30 <= scale <= 2^30 ->
  exists E' T', mulc_p4 (s * 2^63) aExp bExp scale (hh, hl, lh, ll) = f128_pack s E' T' /\ packed s E' T' /\ nn128 E' T'
    /\ E' <= Z.max (aExp + bExp + scale - 16383 + 1) 0 + 1
    /\ (1 <= aExp + bExp + scale - 16383 -> aExp + bExp + scale - 16383 <= 32766 -> aExp + bExp + scale - 16383 <= E').
Proof.
  intros s aExp bExp scale hh hl lh ll Hs Hhh Hhl Hlh Hll HP HaE HbE Hsum Hsc.
  assert (H49 : hh < 2^49) by lia.
  unfold mulc_p4. rewrite add64_small by lia. change 0x3fff with 16383. change 0x7fff with 32767.
  rewrite (shl64_small hh 15) by lia. rewrite is_neg64_val by lia.
  destruct (Z.leb_spec (2^63) (hh * 2^15)) as [TOP|TOP].
  - destruct (Z.ltb_spec (aExp + bExp + (scale - 16383) + 1) 32767) as [OV|OV]; cbn [negb].
    + destruct (mul_finish_class s (aExp + bExp + (scale - 16383) + 1) hh hl lh ll) as [E' [T' (E1 & P1 & N1 & B1 & L1)]]; try lia.
      exists E', T'. split; [exact E1|]. split; [exact P1|]. split; [exact N1| split; [lia| intros; lia]].
    + exists 32767, 0. rewrite inf_pack by lia. split; [reflexivity|]. split; [constructor; lia|]. split; [intros _; reflexivity| lia].
  - destruct (shl1_words hh hl lh ll) as (R1 & R2 & R3 & R4 & E2); [lia|lia|lia|lia|].
    cbv zeta.
    set (hh1 := Z.lor (shl64 hh 1) (Z.shiftr hl 63)) in *.
    set (hl1 := Z.lor (shl64 hl 1) (Z.shiftr lh 63)) in *.
    set (lh1 := Z.lor (shl64 lh 1) (Z.shiftr ll 63)) in *.
    set (ll1 := shl64 ll 1) in *. clearbody hh1 hl1 lh1 ll1.
    assert (H49' : hh1 < 2^49) by lia.
    destruct (Z.leb_spec 32767 (aExp + bExp + (scale - 16383))) as [OV|OV].
    + exists 32767, 0. rewrite inf_pack by lia. split; [reflexivity|]. split; [constructor; lia|]. split; [intros _; reflexivity| lia].
    + destruct (mul_finish_class s (aExp + bExp + (scale - 16383)) hh1 hl1 lh1 ll1) as [E' [T' (E1 & P1 & N1 & B1 & L1)]]; try lia.
      exists E', T'. split; [exact E1|]. split; [exact P1|]. split; [exact N1| split; [lia| intros; lia]].
Qed.

(* [comment removed for export] *)
Section tests.
  Variables (s E T : Z).
  Hypothesis PK : packed s E T.
  Let th := T / 2^64.
  Let tl := T mod 2^64.
  Let hi := s * 2^63 + E * 2^48 + th.

  Lemma th_range : 0 <= th < 2^48. Proof. destruct PK. subst th. dlia. Qed.
  Lemma tl_range : 0 <= tl < 2^64. Proof. destruct PK. subst tl. dlia. Qed.
  Lemma T_eq : T = th * 2^64 + tl. Proof. subst th tl. dlia. Qed.

  Lemma abs_hi : Z.land hi ABS_HI = E * 2^48 + th.
  Proof. destruct PK. pose proof th_range. subst hi. apply hiword_abs; lia. Qed.

  Lemma nan_test_false : nn128 E T ->
    (if Z.land hi ABS_HI =? INF_HI then negb (tl =? 0) else negb (Z.land hi ABS_HI <? INF_HI)) = false.
  Proof.
    intros NN. destruct PK. pose proof th_range. pose proof tl_range. pose proof T_eq. rewrite abs_hi, inf_hi_eq.
    destruct (Z.eqb_spec (E * 2^48 + th) (32767 * 2^48)) as [EQ|NE].
    - assert (E = 32767) by lia. rewrite (NN H2) in H1. replace tl with 0 by lia. reflexivity.
    - destruct (Z.ltb_spec (E * 2^48 + th) (32767 * 2^48)); [reflexivity|].
      assert (E = 32767) by lia. rewrite (NN H3) in H1. exfalso. lia.
  Qed.

  Lemma inf_test : nn128 E T -> (Z.lor (Z.lxor (Z.land hi ABS_HI) INF_HI) tl =? 0) = (E =? 32767).
  Proof.
    intros NN. destruct PK. pose proof th_range. pose proof tl_range. pose proof T_eq. rewrite abs_hi, inf_hi_eq.
    rewrite lor_eqb0 by (try apply Z.lxor_nonneg; lia). rewrite lxor_eqb0.
    destruct (Z.eqb_spec E 32767) as [->|NE].
    - rewrite (NN eq_refl) in H1. replace th with 0 by lia. replace tl with 0 by lia. reflexivity.
    - replace (E * 2 ^ 48 + th =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  Qed.

  Lemma inf_test' : nn128 E T -> (Z.lor tl (Z.lxor (Z.land hi ABS_HI) INF_HI) =? 0) = (E =? 32767).
  Proof. intros NN. rewrite Z.lor_comm. apply inf_test. exact NN. Qed.

  Lemma zero_test : (Z.lor tl (Z.land hi ABS_HI) =? 0) = ((E =? 0) && (T =? 0)).
  Proof.
    destruct PK. pose proof th_range. pose proof tl_range. pose proof T_eq. rewrite abs_hi.
    rewrite lor_eqb0 by lia.
    destruct (Z.eqb_spec E 0) as [->|NE]; destruct (Z.eqb_spec T 0) as [T0|T0]; cbn [andb].
    - rewrite T0 in H1. replace tl with 0 by lia. replace th with 0 by lia. reflexivity.
    - destruct (Z.eqb_spec tl 0); destruct (Z.eqb_spec (0 * 2^48 + th) 0); cbn [andb]; try reflexivity. exfalso; lia.
    - rewrite T0 in H1. replace tl with 0 by lia. replace th with 0 by lia. cbn [Z.eqb andb]. apply Z.eqb_neq. lia.
    - destruct (Z.eqb_spec tl 0); [| reflexivity]. cbn [andb]. apply Z.eqb_neq. lia.
  Qed.

  Lemma zero_test' : (Z.lor (Z.land hi ABS_HI) tl =? 0) = ((E =? 0) && (T =? 0)).
  Proof. rewrite Z.lor_comm. apply zero_test. Qed.

  Lemma exp_shr48 : Z.shiftr (Z.land hi ABS_HI) 48 = E.
  Proof. destruct PK. pose proof th_range. rewrite abs_hi, shiftr_div by lia. dlia. Qed.
End tests.

(* [comment removed for export] *)
Definition mulc_net8 (A1 A2 A3 A4 B1 B2 B3 B4 : Z) : Z * Z * Z * Z :=
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

Lemma mulc_net_eq8 : forall ah al bh bl,
  mulc_net ah al bh bl =
  mulc_net8 (Z.lor (Z.shiftr ah 32) 0x10000) (zext32 ah) (Z.shiftr al 32) (zext32 al)
            (Z.lor (Z.shiftr (shl64 bh 15) 32) 0x80000000) (zext32 (Z.lor (Z.shiftr bl 49) (shl64 bh 15)))
            (Z.shiftr (shl64 bl 15) 32) (zext32 (shl64 bl 15)).
Proof. intros. reflexivity. Qed.

Lemma limbA1_impl : forall th, 0 <= th < 2^48 ->
  Z.lor (Z.shiftr (2^48 + th) 32) 0x10000 = Z.lor (Z.shiftr th 32) 0x10000.
Proof.
  intros th Hth. rewrite !shiftr_div by lia. change 0x10000 with (1 * 2^16).
  replace ((2^48 + th) / 2^32) with (1 * 2^16 + th / 2^32) by dlia.
  assert (R : 0 <= th / 2^32 < 2^16) by dlia.
  rewrite <- (lor_low_high 1 (th / 2^32) 16) by lia.
  rewrite <- Z.lor_assoc, Z.lor_diag. reflexivity.
Qed.

Lemma limbA2_impl : forall th, zext32 (2^48 + th) = zext32 th.
Proof. intros. rewrite !zext32_val. replace (2^48 + th) with (th + 2^16 * 2^32) by lia. apply Z_mod_plus_full. Qed.

Lemma shl15_impl : forall th, 0 <= th < 2^48 -> shl64 (2^48 + th) 15 = 1 * 2^63 + th * 2^15.
Proof. intros. rewrite shl64_small by lia. lia. Qed.

Lemma limbB1_impl : forall th, 0 <= th < 2^48 ->
  Z.lor (Z.shiftr (shl64 (2^48 + th) 15) 32) 0x80000000 = Z.lor (Z.shiftr (shl64 th 15) 32) 0x80000000.
Proof.
  intros th Hth. rewrite shl15_impl, (shl64_small th 15), !shiftr_div by lia. change 0x80000000 with (1 * 2^31).
  replace ((1 * 2^63 + th * 2^15) / 2^32) with (1 * 2^31 + th * 2^15 / 2^32) by dlia.
  assert (R : 0 <= th * 2^15 / 2^32 < 2^31) by dlia.
  rewrite <- (lor_low_high 1 (th * 2^15 / 2^32) 31) by lia.
  rewrite <- Z.lor_assoc, Z.lor_diag. reflexivity.
Qed.

Lemma limbB2_impl : forall th tl, 0 <= th < 2^48 -> 0 <= tl < 2^64 ->
  zext32 (Z.lor (Z.shiftr tl 49) (shl64 (2^48 + th) 15)) = zext32 (Z.lor (Z.shiftr tl 49) (shl64 th 15)).
Proof.
  intros th tl Hth Htl. rewrite shl15_impl, (shl64_small th 15) by lia.
  rewrite <- (lor_low_high 1 (th * 2^15) 63) by lia.
  rewrite Z.lor_assoc. rewrite !zext32_val.
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_ones by lia.
  rewrite !Z.land_lor_distr_l.
  replace (Z.land (1 * 2^63) (Z.ones 32)) with 0 by reflexivity. rewrite Z.lor_0_r. reflexivity.
Qed.

Lemma mulc_net_impl_a : forall th tl bh bl, 0 <= th < 2^48 ->
  mulc_net (2^48 + th) tl bh bl = mulc_net th tl bh bl.
Proof. intros. rewrite !mulc_net_eq8, limbA1_impl, limbA2_impl by lia. reflexivity. Qed.

Lemma mulc_net_impl_b : forall ah al th tl, 0 <= th < 2^48 -> 0 <= tl < 2^64 ->
  mulc_net ah al (2^48 + th) tl = mulc_net ah al th tl.
Proof. intros. rewrite !mulc_net_eq8, limbB1_impl, limbB2_impl by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mul_core_class : forall s aExp bExp tha tla thb tlb scale,
  0 <= s <= 1 -> 0 <= tha < 2^48 -> 0 <= tla < 2^64 -> 0 <= thb < 2^48 -> 0 <= tlb < 2^64 ->
  0 <= aExp -> 0 <= bExp -> aExp + bExp < 2^62 -> -2^30 <= scale <= 2^30 ->
  exists E' T', mul_core (s * 2^63) aExp bExp tha tla thb tlb scale = f128_pack s E' T' /\ packed s E' T' /\ nn128 E' T'
    /\ E' <= Z.max (aExp + bExp + scale - 16383 + 1) 0 + 1
    /\ (1 <= aExp + bExp + scale - 16383 -> aExp + bExp + scale - 16383 <= 32766 -> aExp + bExp + scale - 16383 <= E').
Proof.
  intros s aExp bExp tha tla thb tlb scale Hs Htha Htla Hthb Htlb HaE HbE Hsum Hsc.
  rewrite mul_core_restage.
  pose proof (mulc_net_val tha tla thb tlb Htha Htla Hthb Htlb) as NV.
  destruct (mulc_net tha tla thb tlb) as [[[hh hl] lh] ll]. destruct NV as (R1 & R2 & R3 & R4 & E).
  apply mulc_p4_class; try lia.
  rewrite E.
  assert (A : 2^112 <= 2 ^ 112 + tha * 2 ^ 64 + tla < 2^113) by lia.
  assert (B : 2^112 <= 2 ^ 112 + thb * 2 ^ 64 + tlb < 2^113) by lia.
  split.
  - change (2^239) with (2^112 * (2^112 * 2^15)). apply Z.mul_le_mono_nonneg; lia.
  - change (2^241) with (2^113 * (2^113 * 2^15)). apply Z.mul_lt_mono_nonneg; lia.
Qed.

Lemma mul_core_impl_a : forall sg aExp bExp th tl bh bl scale, 0 <= th < 2^48 ->
  mul_core sg aExp bExp (2^48 + th) tl bh bl scale = mul_core sg aExp bExp th tl bh bl scale.
Proof. intros. rewrite !mul_core_restage, mulc_net_impl_a by lia. reflexivity. Qed.

Lemma mul_core_impl_b : forall sg aExp bExp ah al th tl scale, 0 <= th < 2^48 -> 0 <= tl < 2^64 ->
  mul_core sg aExp bExp ah al (2^48 + th) tl scale = mul_core sg aExp bExp ah al th tl scale.
Proof. intros. rewrite !mul_core_restage, mulc_net_impl_b by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma norm_denormal_class : forall T, 0 < T < 2^112 ->
  exists th' tl' L, norm_denormal (T / 2^64) (T mod 2^64) = (2^48 + th', tl', 127 - L)
    /\ 0 <= th' < 2^48 /\ 0 <= tl' < 2^64 /\ 0 <= L <= 111 /\ 2^L <= T < 2^(L+1)
    /\ 2^112 + th' * 2^64 + tl' = T * 2^(112 - L).
Proof.
  intros T HT.
  set (L := Z.log2 T).
  assert (HL : 2^L <= T < 2^(L+1)). { subst L. destruct (Z.log2_spec T ltac:(lia)). rewrite Z.add_1_r. lia. }
  assert (HL0 : 0 <= L) by (subst L; apply Z.log2_nonneg).
  assert (HL1 : L <= 111). { destruct (Z.le_gt_cases L 111); [lia|]. assert (2^112 <= 2^L) by (apply Z.pow_le_mono_r; lia). lia. }
  clearbody L.
  assert (Hth : 0 <= T / 2^64 < 2^48) by dlia. assert (Htl : 0 <= T mod 2^64 < 2^64) by dlia.
  assert (ET : T / 2^64 * 2^64 + T mod 2^64 = T) by dlia.
  unfold norm_denormal.
  rewrite (clz128_mirror_val (T / 2^64) (T mod 2^64) L) by lia.
  rewrite (sub64_small (127 - L) 15) by lia. replace (127 - L - 15) with (112 - L) by lia.
  pose proof (shl128_mirror_val (T / 2^64) (T mod 2^64) (112 - L) ltac:(lia) Htl ltac:(lia)) as SV.
  assert (TB : (T / 2 ^ 64 * 2 ^ 64 + T mod 2 ^ 64) * 2 ^ (112 - L) < 2 ^ 128).
  { rewrite ET. apply (Z.lt_le_trans _ (2^(L+1) * 2^(112-L))); [apply Z.mul_lt_mono_pos_r; lia|].
    rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
  specialize (SV TB). destruct (shl128_mirror (T / 2^64) (T mod 2^64) (112 - L)) as [nhi nlo].
  destruct SV as (Rh & Rl & EV). rewrite ET in EV.
  assert (LO : 2^112 <= T * 2^(112 - L)).
  { replace (2^112) with (2^L * 2^(112-L)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). apply Z.mul_le_mono_nonneg_r; lia. }
  assert (HI : T * 2^(112 - L) < 2^113).
  { apply (Z.lt_le_trans _ (2^(L+1) * 2^(112-L))); [apply Z.mul_lt_mono_pos_r; lia|].
    rewrite <- Z.pow_add_r by lia. apply Z.eq_le_incl. f_equal. lia. }
  exists (nhi - 2^48), nlo, L. split; [f_equal; f_equal; lia|]. lia.
Qed.

(* [comment removed for export] *)
Theorem f128_mul_class : forall sa Ea Ta sb Eb Tb,
  packed sa Ea Ta -> packed sb Eb Tb -> nn128 Ea Ta -> nn128 Eb Tb ->
  (Ea = 32767 -> ~ (Eb = 0 /\ Tb = 0)) -> (Eb = 32767 -> ~ (Ea = 0 /\ Ta = 0)) ->
  exists E' T', f128_mul (f128_pack sa Ea Ta) (f128_pack sb Eb Tb) = f128_pack (Z.lxor sb sa) E' T'
    /\ packed (Z.lxor sb sa) E' T' /\ nn128 E' T'
    /\ (Ea <= 32766 -> Eb <= 32766 -> E' <= Z.max (Ea + Eb - 16382) 0 + 1)
    /\ (1 <= Ea <= 32766 -> 1 <= Eb <= 32766 -> 16384 <= Ea + Eb <= 49149 -> Ea + Eb - 16383 <= E').
Proof.
  intros sa Ea Ta sb Eb Tb PA PB NA NB XA XB.
  pose proof PA as [Hsa HEa HTa]. pose proof PB as [Hsb HEb HTb].
  pose proof (T_split Ta HTa) as (Htha & Htla & ETa). pose proof (T_split Tb HTb) as (Hthb & Htlb & ETb).
  pose proof (xorbit01 sa sb Hsa Hsb) as Hx.
  unfold f128_mul.
  rewrite !f128_pack_hi, !f128_pack_lo by assumption.
  rewrite !hiword_exp by lia.
  rewrite Z.shiftr_lxor, !hiword_sign by lia.
  rewrite (shl64_small (Z.lxor sb sa) 63) by lia.
  rewrite !hiword_frac by lia.
  rewrite !add64_val. change 0xffffffffffff8001 with (2^64 - 32767). change 0xffffffffffff8002 with (2^64 - 32766).
  set (s' := Z.lxor sb sa) in *.
  rewrite (nan_test_false sa Ea Ta PA NA), (nan_test_false sb Eb Tb PB NB).
  rewrite (inf_test sa Ea Ta PA NA), (inf_test sb Eb Tb PB NB).
  rewrite (zero_test sa Ea Ta PA), (zero_test sb Eb Tb PB).
  rewrite (exp_shr48 sa Ea Ta PA), (exp_shr48 sb Eb Tb PB).
  (* [comment removed for export] *)
  match goal with |- context [negb ?c] => replace (negb c) with ((1 <=? Ea) && (Ea <=? 32766) && (1 <=? Eb) && (Eb <=? 32766)) end.
  2:{ destruct (Z.eq_dec Ea 32767) as [->|NEa].
      - change ((32767 + (2 ^ 64 - 32767)) mod 2 ^ 64) with 0. cbn. destruct (1 <=? Eb); destruct (Eb <=? 32766); reflexivity.
      - rewrite (Z.mod_small (Ea + _)) by lia.
        destruct (Z.eq_dec Eb 32767) as [->|NEb].
        + change ((32767 + (2 ^ 64 - 32767)) mod 2 ^ 64) with 0.
          replace (0 <=? 2^64 - 32767) with true by reflexivity. rewrite Bool.orb_true_r. cbn [negb].
          replace (32767 <=? 32766) with false by reflexivity. rewrite !Bool.andb_false_r. reflexivity.
        + rewrite (Z.mod_small (Eb + _)) by lia.
          destruct (Z.leb_spec 1 Ea); destruct (Z.leb_spec Ea 32766); destruct (Z.leb_spec 1 Eb); destruct (Z.leb_spec Eb 32766); cbn [andb];
          destruct (Z.ltb_spec (Ea + (2 ^ 64 - 32767)) (2 ^ 64 - 32766)); destruct (Z.leb_spec (Eb + (2 ^ 64 - 32767)) (2 ^ 64 - 32767)); cbn; try reflexivity; exfalso; lia. }
  destruct ((1 <=? Ea) && (Ea <=? 32766) && (1 <=? Eb) && (Eb <=? 32766)) eqn:NRM.
  { (* [comment removed for export] *)
    apply andb_prop in NRM. destruct NRM as [NRM N4]. apply andb_prop in NRM. destruct NRM as [NRM N3].
    apply andb_prop in NRM. destruct NRM as [N1 N2].
    apply Z.leb_le in N1. apply Z.leb_le in N2. apply Z.leb_le in N3. apply Z.leb_le in N4.
    destruct (mul_core_class s' Ea Eb (Ta / 2^64) (Ta mod 2^64) (Tb / 2^64) (Tb mod 2^64) 0) as [E' [T' (E1 & P1 & NN1 & B1 & L1)]]; try lia.
    exists E', T'. split; [exact E1|]. split; [exact P1|]. split; [exact NN1|]. split; [intros _ _; lia| intros; lia]. }
  destruct (Z.eqb_spec Ea 32767) as [EA|EA].
  { destruct (Z.eqb_spec Eb 0) as [EB0|EB0]; destruct (Z.eqb_spec Tb 0) as [TB0|TB0]; cbn [andb negb];
    try (exfalso; apply (XA EA); split; assumption).
    all: exists 32767, 0; rewrite inf_pack by lia; split; [reflexivity|]; split; [constructor; lia|]; split; [intros _; reflexivity| split; intros; lia]. }
  destruct (Z.eqb_spec Eb 32767) as [EB|EB].
  { destruct (Z.eqb_spec Ea 0) as [EA0|EA0]; destruct (Z.eqb_spec Ta 0) as [TA0|TA0]; cbn [andb negb];
    try (exfalso; apply (XB EB); split; assumption).
    all: exists 32767, 0; rewrite inf_pack by lia; split; [reflexivity|]; split; [constructor; lia|]; split; [intros _; reflexivity| split; intros; lia]. }
  (* [comment removed for export] *)
  assert (FIN : forall tha tla thb tlb sc,
     0 <= tha < 2^48 -> 0 <= tla < 2^64 -> 0 <= thb < 2^48 -> 0 <= tlb < 2^64 -> -300 <= sc <= 0 ->
     exists E' T', mul_core (s' * 2^63) Ea Eb tha tla thb tlb sc = f128_pack s' E' T' /\ packed s' E' T' /\ nn128 E' T'
       /\ (Ea <= 32766 -> Eb <= 32766 -> E' <= Z.max (Ea + Eb - 16382) 0 + 1)
       /\ (1 <= Ea <= 32766 -> 1 <= Eb <= 32766 -> 16384 <= Ea + Eb <= 49149 -> Ea + Eb - 16383 <= E')).
  { intros tha tla thb tlb sc R1 R2 R3 R4 R5.
    destruct (mul_core_class s' Ea Eb tha tla thb tlb sc) as [E' [T' (E1 & P1 & NN1 & B1 & L1)]]; try lia.
    exists E', T'. split; [exact E1|]. split; [exact P1|]. split; [exact NN1|]. split; [intros _ _; lia|].
    (* [comment removed for export] *)
    intros [Ha1 Ha2] [Hb1 Hb2] _. exfalso.
    replace (1 <=? Ea) with true in NRM by (symmetry; apply Z.leb_le; lia).
    replace (Ea <=? 32766) with true in NRM by (symmetry; apply Z.leb_le; lia).
    replace (1 <=? Eb) with true in NRM by (symmetry; apply Z.leb_le; lia).
    replace (Eb <=? 32766) with true in NRM by (symmetry; apply Z.leb_le; lia).
    discriminate NRM. }
  assert (ZERO : exists E' T', mk128 (s' * 2 ^ 63) 0 = f128_pack s' E' T' /\ packed s' E' T' /\ nn128 E' T'
       /\ (Ea <= 32766 -> Eb <= 32766 -> E' <= Z.max (Ea + Eb - 16382) 0 + 1)
       /\ (1 <= Ea <= 32766 -> 1 <= Eb <= 32766 -> 16384 <= Ea + Eb <= 49149 -> Ea + Eb - 16383 <= E')).
  { exists 0, 0. rewrite zero_pack by lia. split; [reflexivity|]. split; [constructor; lia|]. split; [intros E; lia|]. split; [intros; lia|].
    intros [Ha1 Ha2] [Hb1 Hb2] _. exfalso.
    replace (1 <=? Ea) with true in NRM by (symmetry; apply Z.leb_le; lia).
    replace (Ea <=? 32766) with true in NRM by (symmetry; apply Z.leb_le; lia).
    replace (1 <=? Eb) with true in NRM by (symmetry; apply Z.leb_le; lia).
    replace (Eb <=? 32766) with true in NRM by (symmetry; apply Z.leb_le; lia).
    discriminate NRM. }
  destruct (Z.eqb_spec Ea 0) as [EA0|EA0]; destruct (Z.eqb_spec Ta 0) as [TA0|TA0]; cbn [andb]; [exact ZERO| | |];
  destruct (Z.eqb_spec Eb 0) as [EB0|EB0]; destruct (Z.eqb_spec Tb 0) as [TB0|TB0]; cbn [andb]; try exact ZERO.
  - destruct (norm_denormal_class Ta ltac:(lia)) as [tha' [tla' [La (ENa & R1 & R2 & R3 & R4 & R5)]]]. rewrite ENa.
    destruct (norm_denormal_class Tb ltac:(lia)) as [thb' [tlb' [Lb (ENb & Q1 & Q2 & Q3 & Q4 & Q5)]]]. rewrite ENb.
    rewrite mul_core_impl_a, mul_core_impl_b by lia. apply FIN; lia.
  - destruct (norm_denormal_class Ta ltac:(lia)) as [tha' [tla' [La (ENa & R1 & R2 & R3 & R4 & R5)]]]. rewrite ENa.
    rewrite mul_core_impl_a by lia. apply FIN; lia.
  - destruct (norm_denormal_class Ta ltac:(lia)) as [tha' [tla' [La (ENa & R1 & R2 & R3 & R4 & R5)]]]. rewrite ENa.
    rewrite mul_core_impl_a by lia. apply FIN; lia.
  - destruct (norm_denormal_class Tb ltac:(lia)) as [thb' [tlb' [Lb (ENb & Q1 & Q2 & Q3 & Q4 & Q5)]]]. rewrite ENb.
    rewrite mul_core_impl_b by lia. apply FIN; lia.
  - apply FIN; lia.
  - apply FIN; lia.
  - destruct (norm_denormal_class Tb ltac:(lia)) as [thb' [tlb' [Lb (ENb & Q1 & Q2 & Q3 & Q4 & Q5)]]]. rewrite ENb.
    rewrite mul_core_impl_b by lia. apply FIN; lia.
  - apply FIN; lia.
  - apply FIN; lia.
Qed.
End SF_ClassMul.

(* [comment removed for export] *)
Module SF_ClassAdd.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.Prelim OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.SoftFloat OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.SoftFloatProps OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.SoftFloatProps2 OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.FmtFpDig.SoftFloatProps3 SF_Class SF_ClassMul.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.

Lemma masklo_eq : MASKLO = 2^64 - 1. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma round_mirror_class : forall s aExp SHi SLo,
  0 <= s <= 1 -> 0 <= aExp <= 32766 -> 0 <= SHi < 2^64 -> 0 <= SLo < 2^64 ->
  exists E' T', round_mirror SHi SLo aExp (s * 2^63) = f128_pack s E' T' /\ packed s E' T' /\ nn128 E' T'
    /\ aExp <= E' <= aExp + 1.
Proof.
  intros s aExp SHi SLo Hs HE HSH HSL. unfold round_mirror.
  set (resLo0 := Z.lor (Z.shiftr SLo 3) (shl64 SHi 61)).
  assert (RL0 : 0 <= resLo0 < 2^64).
  { subst resLo0. apply lor_bound; [lia| apply shr_bound64; lia| apply shl64_range; lia]. }
  rewrite masklo_eq, land_ones_mod, (Z.mod_small resLo0) by lia.
  rewrite (shl64_small aExp 48) by lia.
  rewrite (lor_low_high s (aExp * 2^48) 63) by lia.
  rewrite land_mask48. pose proof (Z.mod_pos_bound (Z.shiftr SHi 3) (2^48) ltac:(lia)) as FR.
  set (fr := Z.shiftr SHi 3 mod 2^48) in *.
  replace (s * 2^63 + aExp * 2^48) with ((s * 2^15 + aExp) * 2^48) by lia.
  rewrite (lor_high_low (s * 2^15 + aExp) fr 48) by lia.
  match goal with |- context [add64 resLo0 ?i] => set (inc := i) end.
  assert (INC : 0 <= inc <= 1).
  { subst inc. destruct (negb _).
    - rewrite b2z_val. destruct (negb _); lia.
    - change (Z.land resLo0 1) with (Z.land resLo0 (2^1 - 1)). rewrite land_ones_mod by lia. dlia. }
  pose proof (L_addc resLo0 inc RL0 ltac:(lia)) as (E1 & R1 & C1).
  unfold ltu64 in E1, C1. rewrite add64_val.
  rewrite (Z.mod_small ((s * 2 ^ 15 + aExp) * 2 ^ 48 + fr + _)) by lia.
  rewrite mk128_val by lia.
  destruct (pack_V s ((aExp * 2^48 + fr) * 2^64 + resLo0 + inc) (aExp + 1)) as (EP & PP & BP & ZP); [lia|lia|lia|].
  eexists _, _. split; [rewrite <- EP; lia|]. split; [exact PP|]. split; [intros E32; apply ZP; lia| dlia].
Qed.

(* [comment removed for export] *)
Lemma land_range64 : forall m x, 0 <= x < 2^64 -> 0 <= m -> 0 <= Z.land m x < 2^64.
Proof.
  intros m x Hx Hm. split; [apply Z.land_nonneg; lia|].
  destruct (Z.eq_dec (Z.land m x) 0) as [->|NZ]; [lia|].
  apply Z.log2_lt_pow2; [pose proof (Z.land_nonneg m x); lia|].
  eapply Z.le_lt_trans; [apply Z.log2_land; lia|].
  destruct (Z.eq_dec x 0) as [->|]; [rewrite Z.land_0_r in NZ; lia|].
  apply Z.min_lt_iff. right. apply Z.log2_lt_pow2; lia.
Qed.

Lemma b2z_range : forall b, 0 <= b2z b <= 1.
Proof. intros b. rewrite b2z_val. destruct b; lia. Qed.

Lemma sub64_range : forall x y, 0 <= sub64 x y < 2^64.
Proof. intros. rewrite sub64_val. apply Z.mod_pos_bound. lia. Qed.
Lemma add64_range : forall x y, 0 <= add64 x y < 2^64.
Proof. intros. rewrite add64_val. apply Z.mod_pos_bound. lia. Qed.

Local Ltac rng :=
  first [ apply lor_bound; [lia| rng| rng]
        | apply shl64_range; apply Z.land_nonneg; lia
        | apply shl64_range; lia
        | apply shr_bound64; [rng| apply Z.land_nonneg; lia]
        | apply shr_bound64; [rng| lia]
        | apply land_range64; [rng| lia]
        | apply sub64_range | apply add64_range
        | pose proof (b2z_range ltac:(assumption)); lia
        | lia ].

Lemma align_mirror_range : forall aExp bExp h l, 0 <= h < 2^64 -> 0 <= l < 2^64 ->
  let '(BHi, BLo) := align_mirror aExp bExp h l in 0 <= BHi < 2^64 /\ 0 <= BLo < 2^64.
Proof.
  intros aExp bExp h l Hh Hl. unfold align_mirror.
  destruct (aExp =? bExp); [lia|]. destruct (127 <? sub64 aExp bExp); [lia|]. cbv zeta.
  split.
  - apply land_range64; [| ]. { apply shr_bound64; [lia| apply Z.land_nonneg; lia]. }
    rewrite smask64_val by apply sub64_range. destruct (_ <=? _); [rewrite ones64_eq|]; lia.
  - apply lor_bound; [lia| |].
    + destruct (is_neg64 _); rng.
    + rewrite b2z_val. destruct (negb _); lia.
Qed.

(* [comment removed for export] *)
Lemma addsub_mirror_class : forall sub AHi ALo BHi BLo e,
  0 <= AHi < 2^64 -> 0 <= ALo < 2^64 -> 0 <= BHi < 2^64 -> 0 <= BLo < 2^64 -> 116 <= e < 2^62 ->
  match addsub_mirror sub AHi ALo BHi BLo e with
  | None => True
  | Some (SHi, SLo, e') => 0 <= SHi < 2^64 /\ 0 <= SLo < 2^64 /\ e - 115 <= e' <= e + 1
  end.
Proof.
  intros sub AHi ALo BHi BLo e HA HAL HB HBL He. unfold addsub_mirror. cbv zeta.
  destruct (negb (sub =? 0)).
  - destruct (Z.eqb_spec (Z.lor (Z.lxor ALo BLo) (Z.lxor AHi BHi)) 0) as [Z0|NZ]; [exact I|].
    set (SHi := sub64 (sub64 AHi BHi) (b2z (ALo <? BLo))). set (SLo := sub64 ALo BLo).
    assert (RH : 0 <= SHi < 2^64) by apply sub64_range. assert (RL : 0 <= SLo < 2^64) by apply sub64_range.
    destruct (Z.eqb_spec (Z.shiftr SHi 51) 0) as [S51|S51]; [| lia].
    assert (SH51 : SHi < 2^51). { rewrite shiftr_div in S51 by lia. dlia. }
    (* [comment removed for export] *)
    assert (VNZ : 0 < SHi * 2^64 + SLo).
    { destruct (Z.eq_dec (SHi * 2^64 + SLo) 0) as [V0|]; [| lia]. exfalso. apply NZ.
      assert (SLo = 0) by lia. assert (SHi = 0) by lia.
      assert (EL : ALo = BLo). { subst SLo. rewrite sub64_val in H. dlia. }
      assert (EH : AHi = BHi).
      { subst SHi. rewrite EL in H0. replace (BLo <? BLo) with false in H0 by (symmetry; apply Z.ltb_irrefl).
        change (b2z false) with 0 in H0. rewrite !sub64_val in H0. rewrite Z.sub_0_r, Z.mod_mod in H0 by lia. dlia. }
      rewrite EL, EH, !Z.lxor_nilpotent. reflexivity. }
    set (L := Z.log2 (SHi * 2^64 + SLo)).
    assert (HL : 2^L <= SHi * 2^64 + SLo < 2^(L+1)). { subst L. destruct (Z.log2_spec _ VNZ). rewrite Z.add_1_r. lia. }
    assert (HL0 : 0 <= L) by (subst L; apply Z.log2_nonneg).
    assert (HL1 : L <= 114). { destruct (Z.le_gt_cases L 114); [lia|]. assert (2^115 <= 2^L) by (apply Z.pow_le_mono_r; lia). lia. }
    clearbody L.
    rewrite (clz128_mirror_val SHi SLo L) by lia.
    rewrite (sub64_small (127 - L) 12) by lia.
    pose proof (shl128_mirror_val SHi SLo (127 - L - 12) ltac:(lia) ltac:(lia) ltac:(lia)) as SV.
    assert (TB : (SHi * 2^64 + SLo) * 2^(127 - L - 12) < 2^128).
    { apply (Z.lt_le_trans _ (2^(L+1) * 2^(127 - L - 12))); [apply Z.mul_lt_mono_pos_r; lia|].
      rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
    specialize (SV TB). destruct (shl128_mirror SHi SLo (127 - L - 12)) as [nhi nlo]. destruct SV as (R1 & R2 & _).
    rewrite sub64_small by lia. lia.
  - set (SLo := add64 BLo ALo). assert (RL : 0 <= SLo < 2^64) by apply add64_range.
    set (SHi := add64 (add64 BHi AHi) (b2z (SLo <? BLo))). assert (RH : 0 <= SHi < 2^64) by apply add64_range.
    destruct (is_neg64 (shl64 SHi 11)).
    + split; [rng|]. split; [rng|]. rewrite add64_small by lia. lia.
    + lia.
Qed.

(* [comment removed for export] *)
Definition add_core (xLo xHi yLo yHi aHi bHi : Z) : Z :=
  let aExp := Z.shiftr (shl64 xHi 1) 49 in
  let bExp := Z.shiftr (shl64 yHi 1) 49 in
  let aSigHi := Z.land xHi MASK48 in
  let aSigLo := xLo in
  let bSigHi := Z.land yHi MASK48 in
  let bSigLo := yLo in
  let '(aSigHi, aSigLo, aExp) :=
      if Z.eqb aExp 0 then normalize_mirror aSigHi aSigLo else (aSigHi, aSigLo, aExp) in
  let '(bSigHi, bSigLo, bExp) :=
      if Z.eqb bExp 0 then normalize_mirror bSigHi bSigLo else (bSigHi, bSigLo, bExp) in
  let subtraction := Z.shiftr (Z.lxor bHi aHi) 63 in
  let aSigHi3 := Z.lor (shl64 aSigHi 3) (Z.shiftr aSigLo 61) in
  let bSigHi3 := Z.lor (shl64 bSigHi 3) (Z.lor (Z.shiftr bSigLo 61) IMPL3_HI) in
  let bSigLo3 := shl64 bSigLo 3 in
  let AHi := Z.lor aSigHi3 IMPL3_HI in
  let ALo := shl64 aSigLo 3 in
  let '(BHi, BLo) := align_mirror aExp bExp bSigHi3 bSigLo3 in
  match addsub_mirror subtraction AHi ALo BHi BLo aExp with
  | None => mk128 0 0
  | Some (SHi, SLo, aExp) =>
      let signHi := shl64 (Z.shiftr xHi 63) 63 in
      if negb (lt_s64 aExp 0x7fff) then mk128 (Z.lor signHi INF_HI) 0
      else
        let '(SHi, SLo, aExp) :=
            if negb (lt_s64 0 aExp)
            then (let '(SHi, SLo) := denorm_mirror SHi SLo aExp in (SHi, SLo, 0))
            else (SHi, SLo, aExp) in
        round_mirror SHi SLo aExp signHi
  end.


Lemma add_main_restage : forall aLo aHi bLo bHi aAbsHi bAbsHi,
  add_main aLo aHi bLo bHi aAbsHi bAbsHi =
  if (if bAbsHi =? aAbsHi then aLo <? bLo else aAbsHi <? bAbsHi)
  then add_core bLo bHi aLo aHi aHi bHi else add_core aLo aHi bLo bHi aHi bHi.
Proof. intros. unfold add_main, add_core. destruct (if bAbsHi =? aAbsHi then aLo <? bLo else aAbsHi <? bAbsHi); reflexivity. Qed.

(* [comment removed for export] *)
Lemma add_core_class : forall sx Ex Tx sy Ey Ty aHi bHi,
  packed sx Ex Tx -> packed sy Ey Ty -> 117 <= Ex <= 32766 -> 117 <= Ey <= 32766 ->
  exists s' E' T',
    add_core (Tx mod 2^64) (sx * 2^63 + Ex * 2^48 + Tx / 2^64) (Ty mod 2^64) (sy * 2^63 + Ey * 2^48 + Ty / 2^64) aHi bHi
      = f128_pack s' E' T' /\ packed s' E' T' /\ nn128 E' T'
    /\ ((E' = 0 /\ T' = 0) \/ Ex - 115 <= E' <= Ex + 2).
Proof.
  intros sx Ex Tx sy Ey Ty aHi bHi PX PY HEx HEy.
  pose proof PX as [Hsx HEx' HTx]. pose proof PY as [Hsy HEy' HTy].
  pose proof (T_split Tx HTx) as (Hthx & Htlx & ETx). pose proof (T_split Ty HTy) as (Hthy & Htly & ETy).
  unfold add_core.
  rewrite !hiword_exp, !hiword_frac, !hiword_sign by lia.
  replace (Ex =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Ey =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv zeta.
  match goal with |- context [align_mirror Ex Ey ?h ?l] =>
    pose proof (align_mirror_range Ex Ey h l) as AR;
    destruct (align_mirror Ex Ey h l) as [BHi BLo] end.
  destruct AR as [RBH RBL].
  { apply lor_bound; [lia| apply shl64_range; lia| apply lor_bound; [lia| apply shr_bound64; lia| rewrite impl3_hi_eq; lia]]. }
  { apply shl64_range; lia. }
  match goal with |- context [addsub_mirror ?sb ?ah ?al BHi BLo Ex] =>
    pose proof (addsub_mirror_class sb ah al BHi BLo Ex) as AS;
    destruct (addsub_mirror sb ah al BHi BLo Ex) as [[[SHi SLo] e']|] end.
  - destruct AS as (RSH & RSL & RE).
    { apply lor_bound; [lia| apply lor_bound; [lia| apply shl64_range; lia| apply shr_bound64; lia] | rewrite impl3_hi_eq; lia]. }
    { apply shl64_range; lia. } { lia. } { lia. } { lia. }
    rewrite !lt_s64_val by lia.
    replace (2 ^ 63 <=? e') with false by (symmetry; apply Z.leb_gt; lia).
    change (2 ^ 63 <=? 32767) with false. change (2 ^ 63 <=? 0) with false. cbv iota.
    rewrite (shl64_small sx 63) by lia.
    destruct (Z.ltb_spec e' 32767) as [OV|OV]; cbn [negb].
    + replace (0 <? e') with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
      destruct (round_mirror_class sx e' SHi SLo) as [E' [T' (E1 & P1 & N1 & B1)]]; try lia.
      exists sx, E', T'. split; [exact E1|]. split; [exact P1|]. split; [exact N1|]. right. lia.
    + exists sx, 32767, 0. rewrite inf_pack by lia. split; [reflexivity|]. split; [constructor; lia|]. split; [intros _; reflexivity|]. right. lia.
  - exists 0, 0, 0. change (mk128 0 0) with 0. unfold f128_pack. split; [lia|]. split; [constructor; lia|]. split; [intros E; lia|]. left. lia.
Qed.

(* [comment removed for export] *)
Lemma speck_eq : SPEC_K = 2^63 + 2^48. Proof. reflexivity. Qed.

Theorem f128_add_class : forall L H sa Ea Ta sb Eb Tb,
  packed sa Ea Ta -> packed sb Eb Tb ->
  ((Ea = 0 /\ Ta = 0) \/ (L <= Ea <= H)) -> ((Eb = 0 /\ Tb = 0) \/ (L <= Eb <= H)) -> 117 <= L -> H <= 32766 ->
  exists s' E' T', f128_add (f128_pack sa Ea Ta) (f128_pack sb Eb Tb) = f128_pack s' E' T' /\ packed s' E' T' /\ nn128 E' T'
    /\ ((E' = 0 /\ T' = 0) \/ (L - 115 <= E' <= H + 2)).
Proof.
  intros L H sa Ea Ta sb Eb Tb PA PB CA CB HL HH.
  pose proof PA as [Hsa HEa HTa]. pose proof PB as [Hsb HEb HTb].
  pose proof (T_split Ta HTa) as (Htha & Htla & ETa). pose proof (T_split Tb HTb) as (Hthb & Htlb & ETb).
  assert (NA : nn128 Ea Ta) by (intros E; lia). assert (NB : nn128 Eb Tb) by (intros E; lia).
  unfold f128_add.
  rewrite !f128_pack_hi, !f128_pack_lo by assumption. cbv zeta.
  rewrite (nan_test_false sa Ea Ta PA NA), (nan_test_false sb Eb Tb PB NB).
  rewrite (inf_test' sa Ea Ta PA NA), (inf_test' sb Eb Tb PB NB).
  rewrite (zero_test sa Ea Ta PA), (zero_test sb Eb Tb PB).
  replace (Ea =? 32767) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Eb =? 32767) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite !(abs_hi sa Ea Ta PA), !(abs_hi sb Eb Tb PB).
  (* [comment removed for export] *)
  match goal with |- context [(if Ea * 2^48 + Ta / 2^64 =? 0 then ?x else ?y) || ?z] =>
    replace (if Ea * 2^48 + Ta / 2^64 =? 0 then x else y) with ((Ea =? 0) && (Ta =? 0));
    [ replace z with ((Eb =? 0) && (Tb =? 0)) | ] end.
  3:{ destruct (Z.eqb_spec (Ea * 2^48 + Ta / 2^64) 0) as [Z0|NZ].
      - assert (Ea = 0) by lia. rewrite H0. cbn [Z.eqb andb]. apply eq_true_iff_eq. rewrite !Z.eqb_eq. lia.
      - rewrite speck_eq, add64_small by lia. destruct CA as [[-> ->]|CA]; [exfalso; cbn in NZ; lia|].
        replace (Ea =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. symmetry. apply Z.ltb_ge. lia. }
  2:{ rewrite speck_eq, add64_small by lia.
      destruct (Z.eqb_spec (Eb * 2 ^ 48 + Tb / 2 ^ 64 + (2 ^ 63 + 2 ^ 48)) (2 ^ 63 + 2 ^ 48)) as [Z0|NZ].
      - assert (Eb = 0) by lia. rewrite H0. cbn [Z.eqb andb]. apply eq_true_iff_eq. rewrite !Z.eqb_eq. lia.
      - destruct CB as [[-> ->]|CB]; [exfalso; cbn in NZ; lia|].
        replace (Eb =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
        replace (2 ^ 63 + 2 ^ 48 <? Eb * 2 ^ 48 + Tb / 2 ^ 64 + (2 ^ 63 + 2 ^ 48)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  assert (MAIN : L <= Ea <= H -> L <= Eb <= H -> exists s' E' T',
    add_main (Ta mod 2 ^ 64) (sa * 2 ^ 63 + Ea * 2 ^ 48 + Ta / 2 ^ 64) (Tb mod 2 ^ 64) (sb * 2 ^ 63 + Eb * 2 ^ 48 + Tb / 2 ^ 64)
             (Ea * 2 ^ 48 + Ta / 2 ^ 64) (Eb * 2 ^ 48 + Tb / 2 ^ 64) = f128_pack s' E' T'
    /\ packed s' E' T' /\ nn128 E' T' /\ (E' = 0 /\ T' = 0 \/ L - 115 <= E' <= H + 2)).
  { intros BA BB. rewrite add_main_restage.
    destruct (if _ =? _ then _ else _).
    - destruct (add_core_class sb Eb Tb sa Ea Ta (sa * 2 ^ 63 + Ea * 2 ^ 48 + Ta / 2 ^ 64) (sb * 2 ^ 63 + Eb * 2 ^ 48 + Tb / 2 ^ 64) PB PA)
        as [s' [E' [T' (E1 & P1 & N1 & B1)]]]; [lia|lia|].
      exists s', E', T'. split; [exact E1|]. split; [exact P1|]. split; [exact N1|]. lia.
    - destruct (add_core_class sa Ea Ta sb Eb Tb (sa * 2 ^ 63 + Ea * 2 ^ 48 + Ta / 2 ^ 64) (sb * 2 ^ 63 + Eb * 2 ^ 48 + Tb / 2 ^ 64) PA PB)
        as [s' [E' [T' (E1 & P1 & N1 & B1)]]]; [lia|lia|].
      exists s', E', T'. split; [exact E1|]. split; [exact P1|]. split; [exact N1|]. lia. }
  destruct CA as [[EA0 TA0]|CA].
  - rewrite EA0, TA0 in *. change (0 / 2^64) with 0. change (0 mod 2^64) with 0. cbn [Z.eqb andb orb].
    destruct CB as [[EB0 TB0]|CB].
    + rewrite EB0, TB0 in *. change (0 / 2^64) with 0. change (0 mod 2^64) with 0. cbn [Z.eqb andb orb negb].
      rewrite !Z.mul_0_l, !Z.add_0_r. change (Z.land 0 0) with 0.
      assert (SS : exists s', 0 <= s' <= 1 /\ Z.land (sb * 2^63) (sa * 2^63) = s' * 2^63).
      { assert (Da : sa = 0 \/ sa = 1) by lia. assert (Db : sb = 0 \/ sb = 1) by lia.
        destruct Da as [-> | ->]; destruct Db as [-> | ->]; cbn; (exists 0 + exists 1); split; try lia; reflexivity. }
      destruct SS as [s' [Hs' ->]]. exists s', 0, 0. rewrite zero_pack by lia.
      split; [reflexivity|]. split; [constructor; lia|]. split; [intros E; lia|]. left; lia.
    + replace ((Eb =? 0) && (Tb =? 0)) with false.
      2:{ symmetry. destruct (Z.eqb_spec Eb 0); [exfalso; lia| reflexivity]. }
      cbn [negb]. exists sb, Eb, Tb. rewrite mk128_val by lia. unfold f128_pack.
      split; [lia|]. split; [exact PB|]. split; [exact NB|]. right; lia.
  - replace ((Ea =? 0) && (Ta =? 0)) with false.
    2:{ symmetry. destruct (Z.eqb_spec Ea 0); [exfalso; lia| reflexivity]. }
    cbn [orb]. destruct CB as [[EB0 TB0]|CB].
    + rewrite EB0, TB0 in *. change (0 / 2^64) with 0. change (0 mod 2^64) with 0. cbn [Z.eqb andb orb negb].
      exists sa, Ea, Ta. rewrite mk128_val by lia. unfold f128_pack.
      split; [lia|]. split; [exact PA|]. split; [exact NA|]. right; lia.
    + replace ((Eb =? 0) && (Tb =? 0)) with false.
      2:{ symmetry. destruct (Z.eqb_spec Eb 0); [exfalso; lia| reflexivity]. }
      cbn [negb]. apply MAIN; lia.
Qed.

(* [comment removed for export] *)
Lemma neg_pack : forall s E T, packed s E T ->
  mk128 (Z.lxor (hi64 (f128_pack s E T)) SIGN64) (lo64 (f128_pack s E T)) = f128_pack (1 - s) E T.
Proof.
  intros s E T PK. pose proof PK as [Hs HE HT]. pose proof (T_split T HT) as (Hth & Htl & ET).
  rewrite f128_pack_hi, f128_pack_lo by assumption. rewrite sign64_eq.
  assert (Ds : s = 0 \/ s = 1) by lia.
  destruct Ds as [-> | ->].
  - rewrite lxor_bit_clear; [| lia| lia| rewrite Z.div_small by lia; reflexivity].
    rewrite mk128_val by lia. unfold f128_pack. lia.
  - rewrite lxor_bit_set; [| lia| lia| replace ((1 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64) / 2 ^ 63) with 1 by dlia; reflexivity].
    rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

Theorem f128_sub_class : forall L H sa Ea Ta sb Eb Tb,
  packed sa Ea Ta -> packed sb Eb Tb ->
  ((Ea = 0 /\ Ta = 0) \/ (L <= Ea <= H)) -> ((Eb = 0 /\ Tb = 0) \/ (L <= Eb <= H)) -> 117 <= L -> H <= 32766 ->
  exists s' E' T', f128_sub (f128_pack sa Ea Ta) (f128_pack sb Eb Tb) = f128_pack s' E' T' /\ packed s' E' T' /\ nn128 E' T'
    /\ ((E' = 0 /\ T' = 0) \/ (L - 115 <= E' <= H + 2)).
Proof.
  intros L H sa Ea Ta sb Eb Tb PA PB CA CB HL HH. unfold f128_sub. cbv zeta.
  rewrite (neg_pack sb Eb Tb PB).
  apply f128_add_class; auto. destruct PB; constructor; lia.
Qed.
End SF_ClassAdd.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require Import Prelim SoftFloat SoftFloatProps SoftFloatProps2.
Import SF_Class.
Import SF_ClassMul.
Import SF_ClassAdd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.

Lemma divc_wide_range : forall x_hi x_lo A1 A2 A3 A4,
  let '(q_hi, q_lo) := divc_wide x_hi x_lo A1 A2 A3 A4 in 0 <= q_hi < 2^64 /\ 0 <= q_lo < 2^64.
Proof. intros. unfold divc_wide. cbv zeta. split; apply add64_range. Qed.

Lemma divc_full_range : forall xh b_hw blo,
  let '(x_hi, x_lo) := divc_full xh b_hw blo in 0 <= x_hi < 2^64 /\ 0 <= x_lo < 2^64.
Proof. intros. unfold divc_full. cbv zeta. split; [apply sub64_range| apply add64_range]. Qed.

Lemma land_b2z : forall p q, Z.land (b2z p) (b2z q) = b2z (p && q).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma div_round_class : forall s absHi absLo rHi rLo bHi bLo,
  0 <= s <= 1 -> 0 <= absHi < INF_HI -> 0 <= absLo < 2^64 ->
  exists V', div_round (s * 2^63) absHi absLo rHi rLo bHi bLo = s * 2^127 + V'
    /\ absHi * 2^64 + absLo <= V' <= absHi * 2^64 + absLo + 3 /\ V' <= INF_HI * 2^64.
Proof.
  intros s absHi absLo rHi rLo bHi bLo Hs HH HL. rewrite inf_hi_eq in *.
  unfold div_round. rewrite !inf_hi_eq.
  (* [comment removed for export] *)
  match goal with |- context [add64 absLo (b2z ?g)] => set (gt1 := b2z g) end.
  assert (G1 : 0 <= gt1 <= 1) by (subst gt1; apply b2z_range).
  pose proof (L_addc absLo gt1 HL ltac:(lia)) as (E1 & R1 & C1). unfold ltu64 in E1, C1.
  set (abs1Lo := add64 absLo gt1) in *. set (ca := b2z (abs1Lo <? absLo)) in *.
  rewrite (add64_small absHi ca) by lia.
  (* [comment removed for export] *)
  match goal with |- context [Z.land (b2z (absHi + ca <? ?k)) (b2z ?g)] => set (gt3 := g) end.
  rewrite land_b2z. set (inc2 := b2z ((absHi + ca <? 32767 * 2^48) && gt3)).
  assert (I2 : 0 <= inc2 <= 1 /\ (inc2 = 1 -> absHi + ca < 32767 * 2^48)).
  { subst inc2. rewrite b2z_val. destruct (Z.ltb_spec (absHi + ca) (32767 * 2^48)); destruct gt3; cbn; lia. }
  pose proof (L_addc abs1Lo inc2 R1 ltac:(lia)) as (E2 & R2 & C2). unfold ltu64 in E2, C2.
  set (abs2Lo := add64 abs1Lo inc2) in *. set (cb := b2z (abs2Lo <? abs1Lo)) in *.
  rewrite (add64_small (absHi + ca) cb) by lia.
  (* [comment removed for export] *)
  match goal with |- context [Z.land (b2z (absHi + ca + cb <? ?k)) (b2z ?g)] => set (gt5 := g) end.
  rewrite land_b2z. set (inc3 := b2z ((absHi + ca + cb <? 32767 * 2^48) && gt5)).
  assert (I3 : 0 <= inc3 <= 1 /\ (inc3 = 1 -> absHi + ca + cb < 32767 * 2^48)).
  { subst inc3. rewrite b2z_val. destruct (Z.ltb_spec (absHi + ca + cb) (32767 * 2^48)); destruct gt5; cbn; lia. }
  pose proof (L_addc abs2Lo inc3 R2 ltac:(lia)) as (E3 & R3 & C3). unfold ltu64 in E3, C3.
  set (resLo := add64 abs2Lo inc3) in *. set (cc := b2z (resLo <? abs2Lo)) in *.
  rewrite (add64_small (absHi + ca + cb) cc) by lia.
  rewrite lor_low_high by lia. rewrite mk128_val by lia.
  exists ((absHi + ca + cb + cc) * 2^64 + resLo). lia.
Qed.
Lemma divc_tail_class : forall s expM1 q_hi q_lo aLo aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo,
  0 <= s <= 1 -> 2 <= expM1 <= 32765 -> 0 <= q_hi < 2^64 -> 0 <= q_lo < 2^64 ->
  exists E' T', divc_tail (s * 2^63) expM1 q_hi q_lo aLo aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo = f128_pack s E' T'
    /\ packed s E' T' /\ nn128 E' T' /\ expM1 - 1 <= E' <= expM1 + 2.
Proof.
  intros s expM1 q_hi q_lo aLo aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo Hs HE Hqh Hql.
  unfold divc_tail. change 0x7fff with 32767.
  assert (GEN : forall wE q1Hi absLo r2Hi r2Lo, expM1 - 1 <= wE <= expM1 + 1 -> 0 <= absLo < 2^64 ->
    exists E' T', div_round (s * 2 ^ 63) (Z.lor (shl64 (wrap64 wE) 48) (Z.land q1Hi MASK48)) absLo r2Hi r2Lo bSigHiI bLo = f128_pack s E' T'
      /\ packed s E' T' /\ nn128 E' T' /\ expM1 - 1 <= E' <= expM1 + 2).
  { intros wE q1Hi absLo r2Hi r2Lo HwE HaL.
    rewrite wrap64_id, (shl64_small wE 48), land_mask48 by lia.
    pose proof (Z.mod_pos_bound q1Hi (2^48) ltac:(lia)) as FR.
    rewrite (lor_high_low wE (q1Hi mod 2^48) 48) by lia.
    destruct (div_round_class s (wE * 2^48 + q1Hi mod 2^48) absLo r2Hi r2Lo bSigHiI bLo) as [V' (E1 & B1 & B2)]; [lia| rewrite inf_hi_eq; lia| lia|].
    rewrite E1. rewrite inf_hi_eq in B2.
    destruct (pack_V s V' 32767) as (EP & PP & BP & ZP); [lia| lia| lia|].
    eexists _, _. split; [exact EP|]. split; [exact PP|]. split; [intros E32; apply ZP; exact E32|]. dlia. }
  destruct (negb (Z.shiftr q_hi 49 =? 0)); cbv beta iota zeta.
  - replace (negb (expM1 + 1 <? 32767)) with false by (symmetry; rewrite Bool.negb_false_iff; apply Z.ltb_lt; lia).
    replace (negb (expM1 + 1 <=? 0)) with true by (symmetry; rewrite Bool.negb_true_iff; apply Z.leb_gt; lia).
    cbv iota. apply GEN; [lia|]. apply lor_bound; [lia| apply shr_bound64; lia| apply shl64_range; lia].
  - set (wE := (if negb (Z.shiftr q_hi 48 =? 0) then expM1 + 1 else expM1) - 1).
    assert (HwE : expM1 - 1 <= wE <= expM1) by (subst wE; destruct (negb _); lia).
    replace (32767 <=? wE) with false by (symmetry; apply Z.leb_gt; lia).
    replace (negb (wE <=? 0)) with true by (symmetry; rewrite Bool.negb_true_iff; apply Z.leb_gt; lia).
    cbv iota. apply GEN; [lia|]. apply shl64_range. pose proof (b2z_range (Z.shiftr q_hi 48 =? 0)). lia.
Qed.

Theorem f128_div_class : forall sa Ea Ta sb Eb Tb,
  packed sa Ea Ta -> packed sb Eb Tb -> 1 <= Ea <= 32766 -> 1 <= Eb <= 32766 -> -16000 <= Ea - Eb <= 16000 ->
  exists E' T', f128_div (f128_pack sa Ea Ta) (f128_pack sb Eb Tb) = f128_pack (Z.lxor sb sa) E' T'
    /\ packed (Z.lxor sb sa) E' T' /\ nn128 E' T' /\ 16381 + Ea - Eb <= E' <= 16384 + Ea - Eb.
Proof.
  intros sa Ea Ta sb Eb Tb PA PB HEa HEb HD.
  pose proof PA as [Hsa HEa' HTa]. pose proof PB as [Hsb HEb' HTb].
  pose proof (T_split Ta HTa) as (Htha & Htla & ETa). pose proof (T_split Tb HTb) as (Hthb & Htlb & ETb).
  pose proof (xorbit01 sa sb Hsa Hsb) as Hx.
  unfold f128_div.
  rewrite !f128_pack_hi, !f128_pack_lo by assumption.
  rewrite !hiword_exp by lia.
  rewrite Z.shiftr_lxor, !hiword_sign by lia.
  rewrite (shl64_small (Z.lxor sb sa) 63) by lia.
  rewrite !hiword_frac by lia.
  change EXPK with (2^64 - 32767). change EXPK2 with (2^64 - 32766).
  rewrite !add64_val. rewrite !(Z.mod_small (_ + (2^64 - 32767))) by lia.
  replace (Ea + (2 ^ 64 - 32767) <? 2 ^ 64 - 32766) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Eb + (2 ^ 64 - 32767) <=? 2 ^ 64 - 32767) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [orb negb].
  set (s' := Z.lxor sb sa) in *.
  unfold div_core, divc_setup. cbv beta iota zeta.
  match goal with |- context [divc_full ?a ?b ?c] => pose proof (divc_full_range a b c) as FR; destruct (divc_full a b c) as [x_hi x_lo] end.
  match goal with |- context [divc_wide ?a ?b ?c ?d ?e ?f] => pose proof (divc_wide_range a b c d e f) as WR; destruct (divc_wide a b c d e f) as [q_hi q_lo] end.
  destruct WR as [Rqh Rql].
  destruct (divc_tail_class s' (0 + 16382 + (Ea - Eb)) q_hi q_lo (Ta mod 2 ^ 64) (Z.lor (Ta / 2 ^ 64) IMPLICIT_HI)
             (Z.lor (Tb / 2 ^ 64) IMPLICIT_HI) (Tb mod 2 ^ 64) (shl64 (Z.lor (Ta / 2 ^ 64) IMPLICIT_HI) 1)
             (Z.shiftr (Ta mod 2 ^ 64) 63) (shl64 (Ta mod 2 ^ 64) 1)) as [E' [T' (E1 & P1 & N1 & B1)]]; try lia.
  exists E', T'. split; [exact E1|]. split; [exact P1|]. split; [exact N1| lia].
Qed.
