(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim SoftFloat FmtFp FmtFpPre
     SoftFloatProps FmtFpDig FmtFpProps FmtFpRun FmtFpTail.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import FmtFp_split FmtFp_facts FmtFp_facts2 FmtFp_facts3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Opaque zrepeat.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.

Lemma pow10_split : forall a b, 0 <= a -> 0 <= b -> 10^(a + b) = 10^a * 10^b.
Proof. intros. rewrite Z.pow_add_r by lia. reflexivity. Qed.

Lemma carry_noop : forall big d a, znth big d <= 999999999 -> fmt_fp_carry BIG_FUEL (big, d, a) = Some (big, d, a).
Proof.
  intros big d a H. rewrite fmt_fp_carry_eq. unfold BIG_FUEL. cbn [wloop].
  replace (999999999 <? znth big d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma R_spec_gen : forall p1 prefix pl r0 big a z e,
  TS r0 big a z e -> znth big a <> 0 -> (r0 = 0 -> znth big 0 < 2^29) -> (r0 = 122 -> 86 <= a) -> 1 <= p1 <= 26 ->
  exists bigR aR zR eR, g_R CHR_g p1 prefix pl big a r0 z e (g_j CHR_g p1 e) = Some (bigR, aR, zR, eR) /\
    TS r0 bigR aR zR eR /\ znth bigR aR <> 0 /\ (aR = a \/ aR = a - 1) /\ zR <= z.
Proof.
  intros p1 prefix pl r0 big a z e HT NZ B0 A86 Hp.
  pose proof HT as (WB & LB & AZ & Z7 & ZB & R & [k (Hk & Hka & He)]).
  unfold g_j. change (Z.lor CHR_g 32 =? CHR_f) with false. change (Z.lor CHR_g 32 =? CHR_g) with true.
  replace (p1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].
  set (j := p1 - 1 * e - 1).
  unfold g_R.
  destruct (Z.ltb_spec j (9 * (z - r0 - 1))) as [JL|JG].
  2:{ eexists _, _, _, _. split; [reflexivity|]. split; [exact HT|]. split; [exact NZ|]. split; [left; reflexivity| lia]. }
  change LDBL_MAX_EXP with 16384.
  assert (Hj : -1200 <= j <= 1200) by (subst j; lia).
  rewrite Z.quot_div_nonneg by lia. rewrite Z.rem_mod_nonneg by lia.
  set (q := (j + 9 * 16384) / 9 - 16384). set (j2 := (j + 9 * 16384) mod 9).
  assert (Hq : j = 9 * q + j2 /\ 0 <= j2 <= 8) by (subst q j2; dlia).

  set (f := (p1 - k + 9) / 9).
  assert (Hf : q = a - r0 + f - 1 /\ j2 = p1 - k + 9 - 9 * f /\ 0 <= f <= 3).
  { subst f j q j2. rewrite He. dlia. }
  destruct Hf as (Eq & Ej2 & Bf).
  assert (Hd : a <= r0 + 1 + q < z /\ (r0 + 1 + q = a <-> p1 < k)).
  { split; [| subst f; dlia]. split; [lia|]. destruct Hq as [Hq _]. nia. }
  set (d := r0 + 1 + q) in *. destruct Hd as [Hd Hda].
  rewrite (powi_spec j2) by lia.
  set (i := 10 ^ (9 - j2)).
  assert (Hi : 10 <= i <= NB /\ NB = i * 10^j2).
  { subst i. pose proof (pow10_le_NB (9 - j2) ltac:(lia)). pose proof (pow10_le_NB j2 ltac:(lia)).
    split; [| rewrite (NB_multiple (9 - j2)) by lia; f_equal; f_equal; lia].
    split; [| lia]. change 10 with (10^1). apply Z.pow_le_mono_r; lia. }

  assert (Hia : d = a -> 10^(k-1) = i * 10^(p1 - 1) /\ i <= 10^(k-1)).
  { intros Dq. assert (F0 : f = 0) by lia. assert (E9 : 9 - j2 = k - p1) by lia.
    subst i. rewrite E9. split; [rewrite <- pow10_split by lia; f_equal; lia|].
    apply Z.pow_le_mono_r; lia. }
  clearbody i. destruct Hi as [Hi NBi].
  pose proof (WB d) as Wd.
  pose proof (Z.mod_pos_bound (znth big d) i ltac:(lia)) as Xr.
  pose proof (Z.div_mod (znth big d) i ltac:(lia)) as Xd.
  set (x := znth big d mod i) in *.

  assert (LEAD : d = a -> 10^(k-1) <= znth big a - x < 10^k /\ znth big a - x + i <= 10^k).
  { intros Dq. destruct (Hia Dq) as [E1 Ile]. rewrite <- Dq in Hka |- *.
    pose proof (pow10_pos (p1 - 1) ltac:(lia)) as P1.
    assert (D1 : 10^(p1-1) <= znth big d / i) by (apply Z.div_le_lower_bound; [lia| rewrite <- E1; lia]).
    assert (E2 : 10^k = i * (10^(p1-1) * 10)).
    { replace k with ((k-1)+1) at 1 by lia. rewrite pow10_split by lia. rewrite E1. change (10^1) with 10. lia. }
    assert (D2 : znth big d / i < 10^(p1-1) * 10) by (apply Z.div_lt_upper_bound; [lia| rewrite <- E2; lia]).
    assert (M1 : i * 10^(p1-1) <= i * (znth big d / i)) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (M2 : i * (znth big d / i) <= i * (10^(p1-1) * 10 - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
    rewrite <- E1 in M1. rewrite Z.mul_sub_distr_l, <- E2 in M2. lia. }
  destruct (negb (x =? 0) || negb (d + 1 =? z)) eqn:CX.
  2:{
      eexists _, _, _, _. split; [reflexivity|].
      replace (if d + 1 <? z then d + 1 else z) with z by (destruct (Z.ltb_spec (d + 1) z); lia).
      split; [exact HT|]. split; [exact NZ|]. split; [left; reflexivity| lia]. }
  cbv zeta.

  assert (DOWN : exists bigR aR zR eR,
    match Some (zupd big d (znth big d - x), a, d, e) with
    | Some (big0, a0, d0, e0) => Some (big0, a0, if d0 + 1 <? z then d0 + 1 else z, e0)
    | None => None end = Some (bigR, aR, zR, eR) /\
    TS r0 bigR aR zR eR /\ znth bigR aR <> 0 /\ (aR = a \/ aR = a - 1) /\ zR <= z).
  { eexists _, _, _, _. split; [reflexivity|].
    assert (ZR : a < (if d + 1 <? z then d + 1 else z) <= z) by (destruct (Z.ltb_spec (d + 1) z); lia).
    assert (NZ' : znth (zupd big d (znth big d - x)) a <> 0).
    { destruct (Z.eq_dec d a) as [Dq|Dq].
      - rewrite Dq. rewrite znth_zupd_eq by lia. destruct (LEAD Dq) as [L1 _]. pose proof (pow10_pos (k-1) ltac:(lia)). lia.
      - rewrite znth_zupd_neq by lia. exact NZ. }
    split; [| split; [exact NZ'| split; [left; reflexivity| lia]]].
    unfold TS. split; [apply W9_zupd; [exact WB| lia]|]. split; [rewrite zlength_zupd; exact LB|].
    split; [lia|]. split; [lia|]. split; [intros kk Hkk; rewrite znth_zupd_neq by lia; apply ZB; lia|].
    split; [exact R|]. exists k.
    destruct (Z.eq_dec d a) as [Dq|Dq].
    - rewrite Dq. rewrite znth_zupd_eq by lia. destruct (LEAD Dq) as [L1 _]. split; [exact Hk|]. split; [exact L1| exact He].
    - rewrite znth_zupd_neq by lia. split; [exact Hk|]. split; [exact Hka| exact He]. }
  assert (UP : exists bigR aR zR eR,
    match (match fmt_fp_carry BIG_FUEL
             (zupd (zupd big d (znth big d - x)) d (u32 (znth (zupd big d (znth big d - x)) d + i)), d, a) with
           | Some (big0, d0, a0) =>
             match fmt_fp_cnt TEN_FUEL (znth big0 a0) (10, 9 * (r0 - a0)) with
             | Some (_, e0) => Some (big0, a0, d0, e0)
             | None => None
             end
           | None => None end) with
    | Some (big0, a0, d0, e0) => Some (big0, a0, if d0 + 1 <? z then d0 + 1 else z, e0)
    | None => None end = Some (bigR, aR, zR, eR) /\
    TS r0 bigR aR zR eR /\ znth bigR aR <> 0 /\ (aR = a \/ aR = a - 1) /\ zR <= z).
  { rewrite znth_zupd_eq by lia.
    assert (XI : 0 <= znth big d - x /\ znth big d - x + i <= NB).
    { split; [lia|].
      assert (D3 : znth big d / i < 10 ^ j2) by (apply Z.div_lt_upper_bound; [lia|]; rewrite <- NBi; unfold NB in *; lia).
      assert (D4 : i * (znth big d / i) <= i * (10 ^ j2 - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
      rewrite Z.mul_sub_distr_l, <- NBi in D4. lia. }
    rewrite (u32_id (znth big d - x + i)) by (unfold NB in *; lia).
    set (big2 := zupd (zupd big d (znth big d - x)) d (znth big d - x + i)).
    assert (L2 : zlength big2 = 128) by (subst big2; rewrite !zlength_zupd; exact LB).
    assert (B2d : znth big2 d = znth big d - x + i) by (subst big2; rewrite znth_zupd_eq by (rewrite zlength_zupd; lia); reflexivity).
    assert (B2o : forall ii, ii <> d -> znth big2 ii = znth big ii) by (intros ii Hii; subst big2; rewrite !znth_zupd_neq by lia; reflexivity).
    destruct (Z.eq_dec a 0) as [A0|A0].
    - destruct (Z.eq_dec d a) as [Dq|Dq].
      +
        assert (R0 : r0 = 0) by (destruct R as [R0|(_ & Ra & _)]; lia).
        specialize (B0 R0). rewrite <- A0 in B0. rewrite <- Dq in B0.
        assert (SMALL : znth big2 d <= 999999999).
        { rewrite B2d. destruct (Hia Dq) as [_ Ile].
          assert (i <= 10^8) by (apply (Z.le_trans _ _ _ Ile); apply Z.pow_le_mono_r; lia).
          change (10^8) with 100000000 in *. change (2^29) with 536870912 in B0. lia. }
        rewrite (carry_noop big2 d a SMALL).
        pose proof (LEAD Dq) as [L1 L3].
        assert (W2 : W9 big2).
        { intros ii. destruct (Z.eq_dec ii d) as [->|Hne]; [rewrite B2d; unfold NB; lia| rewrite B2o by exact Hne; apply WB]. }
        assert (NZ2 : znth big2 a <> 0). { rewrite <- Dq, B2d. pose proof (pow10_pos (k-1) ltac:(lia)). lia. }
        pose proof (W2 a) as Wa2.
        destruct (cnt_spec (znth big2 a) (9 * (r0 - a)) Wa2) as [kC (ECn & HkC & HhiC & HloC)]. rewrite ECn.
        eexists _, _, _, _. split; [reflexivity|].
        assert (ZR : a < (if d + 1 <? z then d + 1 else z) <= z) by (destruct (Z.ltb_spec (d + 1) z); lia).
        split; [| split; [exact NZ2| split; [left; reflexivity| lia]]].
        unfold TS. split; [exact W2|]. split; [exact L2|]. split; [lia|]. split; [lia|].
        split. { intros kk Hkk. rewrite B2o by lia. apply ZB. lia. }
        split. { exact R. }
        exists kC. split; [exact HkC|]. split; [| lia]. split; [apply HloC; exact NZ2| exact HhiC].
      +
        destruct (carry_spec big2 d a L2 ltac:(lia) ltac:(lia)) as [bigC [dC [aC (EC & LC & WC & AC0 & ACa & DC & VdC & BC & UC & ZC & TC & EQC)]]].
        { intros ii Hii. rewrite B2o by exact Hii. apply WB. }
        { rewrite B2d. lia. }
        { intros _. split; [lia|]. rewrite B2o by lia. destruct R as [R0|[_ ?]]; [| lia]. specialize (B0 R0). unfold NB. lia. }
        rewrite EC.
        assert (NZC : znth bigC aC <> 0).
        { destruct ACa as [->|(-> & -> & V1)]; [| rewrite V1; lia].
          destruct (Z.eq_dec dC a) as [->|]; [lia|]. rewrite UC by lia. rewrite B2o by lia. exact NZ. }
        pose proof (WC aC) as WaC.
        destruct (cnt_spec (znth bigC aC) (9 * (r0 - aC)) WaC) as [kC (ECn & HkC & HhiC & HloC)]. rewrite ECn.
        eexists _, _, _, _. split; [reflexivity|].
        assert (ZR : aC < (if dC + 1 <? z then dC + 1 else z) <= z) by (destruct (Z.ltb_spec (dC + 1) z); lia).
        split; [| split; [exact NZC| split; [destruct ACa as [->|(-> & _)]; [left|right]; reflexivity| lia]]].
        unfold TS. split; [exact WC|]. split; [exact LC|]. split; [lia|]. split; [lia|].
        split. { intros kk Hkk. rewrite BC by lia. rewrite B2o by lia. apply ZB. destruct ACa as [->|(-> & _)]; lia. }
        split. { destruct R as [R0|(R1 & R2)]; [left; exact R0| right]. split; [exact R1|]. specialize (A86 R1). destruct ACa as [->|(-> & _)]; lia. }
        exists kC. split; [exact HkC|]. split; [| lia]. split; [apply HloC; exact NZC| exact HhiC].
    -
      destruct (carry_spec big2 d a L2 ltac:(lia) ltac:(lia)) as [bigC [dC [aC (EC & LC & WC & AC0 & ACa & DC & VdC & BC & UC & ZC & TC & EQC)]]].
      { intros ii Hii. rewrite B2o by exact Hii. apply WB. }
      { rewrite B2d. lia. }
      { intros A00. lia. }
      rewrite EC.
      assert (NZC : znth bigC aC <> 0).
      { destruct ACa as [->|(-> & -> & V1)]; [| rewrite V1; lia].
        destruct (Z.eq_dec dC a) as [->|]; [lia|]. rewrite UC by lia.
        destruct (Z.eq_dec d a) as [Dq|Dq]; [exfalso; lia | rewrite B2o by lia; exact NZ]. }
      pose proof (WC aC) as WaC.
      destruct (cnt_spec (znth bigC aC) (9 * (r0 - aC)) WaC) as [kC (ECn & HkC & HhiC & HloC)]. rewrite ECn.
      eexists _, _, _, _. split; [reflexivity|].
      assert (ZR : aC < (if dC + 1 <? z then dC + 1 else z) <= z) by (destruct (Z.ltb_spec (dC + 1) z); lia).
      split; [| split; [exact NZC| split; [destruct ACa as [->|(-> & _)]; [left|right]; reflexivity| lia]]].
      unfold TS. split; [exact WC|]. split; [exact LC|]. split; [lia|]. split; [lia|].
      split. { intros kk Hkk. rewrite BC by lia. rewrite B2o by lia. apply ZB. destruct ACa as [->|(-> & _)]; lia. }
      split. { destruct R as [R0|(R1 & R2)]; [left; exact R0| right]. split; [exact R1|]. specialize (A86 R1). destruct ACa as [->|(-> & _)]; lia. }
      exists kC. split; [exact HkC|]. split; [| lia]. split; [apply HloC; exact NZC| exact HhiC]. }
  destruct (negb (pl =? 0) && (znth PREFIX_STR prefix =? CHR_minus)); cbv beta iota;
  match goal with |- context [negb (f128_le ?A ?B =? 0)] => destruct (negb (f128_le A B =? 0)) end;
  first [exact DOWN | exact UP].
Qed.

Theorem H_spec_w : forall w o p1 prefix pl r0 big a z e, 0 <= w <= 1 ->
  TS r0 big a z e -> znth big a <> 0 -> 1 <= p1 <= 26 -> 0 <= pl -> 0 <= prefix -> prefix + pl <= 18 ->
  Forall gch (zsub PREFIX_STR prefix pl) ->
  exists txt l', g_H o w 0 CHR_g p1 prefix pl big a r0 z e = Some (o ++ txt, pl + l') /\
    zlength txt = pl + l' /\ Forall gch txt /\ 1 <= l' <= p1 + 7.
Proof.
  intros w o p1 prefix pl r0 big a z e Hw HT NZ Hp Hpl Hpr Hpp Fpre.
  pose proof HT as (WB & LB & AZ & Z7 & ZB & R & [k (Hk & Hka & He)]).
  assert (Hr0 : 0 <= r0 <= 122) by (destruct R as [->|[-> _]]; lia).
  unfold g_H.
  destruct (strip_spec big a z ltac:(lia) ltac:(lia) NZ) as [z' (Es & Hz' & Zs & NZs)]. rewrite Es.
  change (Z.lor CHR_g 32 =? CHR_g) with true. cbv iota.
  replace (p1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (Z.land 0 ALT_FORM =? 0) with true.
  replace ((a <? z') && negb (znth big (z' - 1) =? 0)) with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Z.ltb_lt; lia| apply Bool.negb_true_iff, Z.eqb_neq; exact NZs]. }
  pose proof (WB (z' - 1)) as Wz.
  destruct (fmt_fp_tz_total (znth big (z' - 1)) ltac:(unfold NB in Wz; lia)) as [it [jt Et]]. rewrite Et.
  assert (PL : zlength (zsub PREFIX_STR prefix pl) = pl) by (apply zlength_zsub; [lia|lia| unfold PREFIX_STR, zlength; cbn [length]; lia]).
  destruct ((e <? p1) && (-4 <=? e)) eqn:CF.
  -
    apply andb_prop in CF. destruct CF as [CF1 CF2]. apply Z.ltb_lt in CF1. apply Z.leb_le in CF2.
    change (Z.lor (CHR_g - 1) 32 =? CHR_f) with true. cbv iota.
    set (p2 := Z.min (p1 - (e + 1)) (Z.max 0 (9 * (z' - r0 - 1) - jt))).
    assert (Hp2 : 0 <= p2 <= p1 - (e + 1)) by (subst p2; lia). clearbody p2.
    cbn [negb orb]. rewrite Bool.orb_false_r.
    set (palt := if negb (p2 =? 0) then 1 else 0).
    assert (Hpalt : palt = (if p2 =? 0 then 0 else 1) /\ 0 <= palt <= 1) by (subst palt; destruct (p2 =? 0); cbn; lia).
    destruct Hpalt as [Epalt Bpalt]. clearbody palt.
    replace (INT_MAX - 1 - palt <? p2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    change (CHR_g - 1) with 102. rewrite len_f_spec by lia.
    set (l2 := if 0 <? e then 1 + p2 + palt + e else 1 + p2 + palt).
    assert (Hl2 : l2 = 1 + p2 + palt + Z.max e 0 /\ 1 <= l2 <= p1 + 7) by (subst l2; destruct (Z.ltb_spec 0 e); lia).
    destruct Hl2 as [El2 Bl2]. clearbody l2.
    replace (INT_MAX - pl <? l2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    rewrite pad_exact by lia. rewrite zrepeat_nil by lia. rewrite app_nil_r.
    rewrite pad_flag by (cbv; discriminate).
    change (Z.lor 102 32 =? CHR_f) with true. cbv iota.
    destruct (emit_f_spec (out o (zsub PREFIX_STR prefix pl)) big a r0 z' p2 k WB) as [txt (Ef & Ff & Lf)]; try lia.
    { intros Hra. apply ZB. lia. }
    { right. split; [lia| exact Hka]. }
    rewrite Ef. rewrite pad_flag by (cbv; discriminate).
    exists (zsub PREFIX_STR prefix pl ++ txt), l2. unfold out. rewrite <- app_assoc.
    split; [f_equal; f_equal; lia|]. split.
    + rewrite zlength_app, PL, Lf, El2, Epalt.
      destruct (Z.leb_spec a r0); destruct (Z.eqb_spec p2 0); lia.
    + split; [| exact Bl2]. apply Forall_app. split; [exact Fpre|]. eapply Forall_impl; [| exact Ff]. apply gch_isdigdot.
  -
    change (Z.lor (CHR_g - 2) 32 =? CHR_f) with false. cbv iota.
    set (p2 := Z.min (p1 - 1) (Z.max 0 (9 * (z' - r0 - 1) + e - jt))).
    assert (Hp2 : 0 <= p2 <= p1 - 1) by (subst p2; lia). clearbody p2.
    cbn [negb orb]. rewrite Bool.orb_false_r.
    set (palt := if negb (p2 =? 0) then 1 else 0).
    assert (Hpalt : palt = (if p2 =? 0 then 0 else 1) /\ 0 <= palt <= 1) by (subst palt; destruct (p2 =? 0); cbn; lia).
    destruct Hpalt as [Epalt Bpalt]. clearbody palt.
    replace (INT_MAX - 1 - palt <? p2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    change (CHR_g - 2) with 101.
    pose proof (TS_e_bound _ _ _ _ _ HT) as EB.
    destruct (len_e_spec (1 + p2 + palt) e ltac:(lia) ltac:(lia)) as [estr [eb (El & Hest & Leb & Geb)]]. rewrite El.
    replace (INT_MAX - pl <? 1 + p2 + palt + (12 - estr)) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    rewrite pad_exact by lia. rewrite zrepeat_nil by lia. rewrite app_nil_r.
    rewrite pad_flag by (cbv; discriminate).
    change (Z.lor 101 32 =? CHR_f) with false. cbv iota.
    destruct (emit_e_spec (out o (zsub PREFIX_STR prefix pl)) big a z' p2 eb estr k WB) as [txt (Ee & Fe & Le)]; try lia.
    { right. split; [lia| exact Hka]. }
    rewrite Ee. rewrite pad_flag by (cbv; discriminate).
    exists (zsub PREFIX_STR prefix pl ++ txt ++ zsub eb estr (12 - estr)), (1 + p2 + palt + (12 - estr)). unfold out. rewrite <- !app_assoc.
    split; [f_equal; f_equal; lia|]. split.
    + rewrite !zlength_app, PL, Le, zlength_zsub by lia. rewrite Epalt.
      destruct (Z.ltb_spec 0 p2); destruct (Z.eqb_spec p2 0); lia.
    + split; [| lia]. apply Forall_app. split; [exact Fpre|]. apply Forall_app. split; [eapply Forall_impl; [| exact Fe]; apply gch_isdigdot|].
      apply zsub_Forall; try lia. intros kk Hkk. apply Geb. lia.
Qed.

Lemma ffp_e_eq : ffp_e = g_e. Proof. reflexivity. Qed.
Lemma ffp_j_eq : ffp_j = g_j. Proof. reflexivity. Qed.
Lemma ffp_R_eq : ffp_R = g_R. Proof. reflexivity. Qed.
Lemma ffp_H_eq : ffp_H = g_H. Proof. reflexivity. Qed.

Lemma ffp_sign_0 : forall y, ffp_sign y 0 = if negb (signbitl y =? 0) then (Z.lxor y F128_SIGNBIT, 0, 1) else (y, 1, 0).
Proof. intros. reflexivity. Qed.

Lemma gch_numch : forall c, gch c -> is_numch c = true.
Proof.
  intros c H. unfold is_numch. unfold gch in H.
  destruct H as [H|[->|[->|[->|[->| ->]]]]]; try reflexivity.
  replace (48 <=? c) with true by (symmetry; apply Z.leb_le; lia).
  replace (c <=? 57) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Theorem fmt_fp_g_total6 : forall d w, dfin d -> (w = 0 \/ w = 1) ->
  let p1 := 6 in
  exists txt pl l', fmt_fp [] (f128_of_d d) w p1 0 CHR_g = Some (txt, pl + l') /\
    zlength txt = pl + l' /\ Forall gch txt /\ 0 <= pl <= 1 /\ 1 <= l' <= p1 + 7.
Proof.
  intros d w Hfin Hw p1. assert (Hp : 1 <= p1 <= 26) by (subst p1; lia).
  destruct (fmt_loops d p1 CHR_g Hfin ltac:(lia) ltac:(cbv; discriminate))
    as [nz [fr [e0 [y2 (C1 & C2 & C3 & C4 & REST)]]]].
  cbv zeta in REST. destruct REST as (He2 & [big [z (ED & Hz & WB & LB & ZO & W0 & ZC & [s1 (EU & HS1 & DS1 & ZS1 & [big2 [a2 [z2 (EDN & PN & PZ)]]])])]]).
  rewrite fmt_fp_split, ffp_sign_0.
  set (sb := negb (signbitl (f128_of_d d) =? 0)).
  assert (Y1 : forall prefix pl, (if sb then (Z.lxor (f128_of_d d) F128_SIGNBIT, 0, 1) else (f128_of_d d, 1, 0)) = (strip_sign (f128_of_d d), prefix, pl) ->
     exists txt l', ffp_C [] w 0 CHR_g (strip_sign (f128_of_d d)) p1 prefix pl = Some (txt, pl + l') /\
       zlength txt = pl + l' /\ Forall gch txt /\ 1 <= l' <= p1 + 7).
  2:{ assert (SS : strip_sign (f128_of_d d) = if sb then Z.lxor (f128_of_d d) F128_SIGNBIT else f128_of_d d) by reflexivity.
      destruct sb.
      - destruct (Y1 0 1) as [txt [l' (E & L & F & B)]]; [rewrite SS; reflexivity|].
        rewrite <- SS. replace (fpclassifyl _ <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite E. exists txt, 1, l'. repeat split; auto; lia.
      - destruct (Y1 1 0) as [txt [l' (E & L & F & B)]]; [rewrite SS; reflexivity|].
        rewrite <- SS. replace (fpclassifyl _ <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite E. exists txt, 0, l'. repeat split; auto; lia. }
  intros prefix pl EQ.
  assert (PP : (prefix = 0 /\ pl = 1) \/ (prefix = 1 /\ pl = 0)) by (destruct sb; inversion EQ; lia).
  unfold ffp_C. rewrite C2. cbv zeta. rewrite C3. unfold ffp_C2. rewrite C4.
  replace (p1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct nz.
  -
    cbv iota in ED. cbv iota.
    set (e2 := e0 - 1 - 28) in *.
    unfold ffp_D. change (128 - 5 - 1) with 122.
    set (r0 := if e2 <? 0 then 0 else 122) in *.
    rewrite ED. unfold ffp_E. rewrite EU. unfold ffp_F.
    destruct s1 as [[[b1 a1] z1] e21]. rewrite EDN.
    rewrite ffp_G_eq, ffp_e_eq, ffp_j_eq, ffp_R_eq, ffp_H_eq.
    pose proof (PN eq_refl) as PO.
    destruct (g_e_spec r0 big2 a2 z2 PO) as [e (Ee & TSe)]. rewrite Ee.
    pose proof PO as (_ & _ & _ & _ & NZa & _ & Rr).
    destruct (R_spec_gen p1 prefix pl r0 big2 a2 z2 e TSe NZa) as [bigR [aR [zR [eR (ER & TSR & NZR & AR & ZR)]]]]; [| | lia |].
    { intros R0. destruct Rr as [[_ B]|[R1 _]]; [exact B| lia]. }
    { intros R1. destruct Rr as [[R0 _]|(_ & B & _)]; [lia| lia]. }
    cbv zeta. rewrite ER.
    destruct (H_spec_w w [] p1 prefix pl r0 bigR aR zR eR ltac:(lia) TSR NZR) as [txt [l' (EH & L & F & B)]]; try lia.
    { destruct PP as [[-> ->]|[-> ->]]; cbn; [constructor; [unfold gch; lia| constructor] | constructor]. }
    rewrite EH. exists txt, l'. cbn. repeat split; auto; lia.
  -
    destruct (ZC eq_refl) as (E2 & Ez & Ebig). cbv iota in ED. cbv iota.
    rewrite E2 in *. change (0 <? 0) with false in *. cbv iota in ED. cbv iota.
    unfold ffp_D. change (128 - 5 - 1) with 122. change (0 <? 0) with false. cbv iota.
    rewrite ED. unfold ffp_E. rewrite EU. rewrite (HS1 ltac:(lia)). unfold ffp_F.
    rewrite (HS1 ltac:(lia)) in EDN. rewrite EDN.
    destruct (PZ eq_refl) as (-> & -> & ->).
    assert (G0a : ffp_G [] 0 0 CHR_g 6 0 1 (zrepeat 0 128) 122 122 123 = Some ([45; 48], 2)) by (vm_compute; reflexivity).
    assert (G0b : ffp_G [] 0 0 CHR_g 6 1 0 (zrepeat 0 128) 122 122 123 = Some ([48], 1)) by (vm_compute; reflexivity).
    assert (G1a : ffp_G [] 1 0 CHR_g 6 0 1 (zrepeat 0 128) 122 122 123 = Some ([45; 48], 2)) by (vm_compute; reflexivity).
    assert (G1b : ffp_G [] 1 0 CHR_g 6 1 0 (zrepeat 0 128) 122 122 123 = Some ([48], 1)) by (vm_compute; reflexivity).
    subst p1. destruct Hw as [-> | ->]; destruct PP as [[-> ->]|[-> ->]].
    + rewrite G0a. exists [45; 48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
    + rewrite G0b. exists [48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
    + rewrite G1a. exists [45; 48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
    + rewrite G1b. exists [48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
Qed.

Lemma fmt_fp_dn_iter_eq : forall n p t r s, fmt_fp_dn_iter n p t r s = dn_iter n p t r s.
Proof. reflexivity. Qed.
Lemma ffp_sign_fst : forall y, fst (fst (ffp_sign y 0)) = strip_sign y.
Proof. intros y. unfold ffp_sign, strip_sign. destruct (negb (signbitl y =? 0)); reflexivity. Qed.

Definition fmt_fp_facts (y fl p t : Z) : Prop :=
  yn_fact y /\ yn_fact (Z.lxor y F128_SIGNBIT)
  /\ dig_words_fact y fl /\ e2_range_fact y fl /\ dn_phase_fact y fl p t
  /\ words_all_fact y fl p t /\ carry_fact y fl p t /\ azr_fact y fl p t
  /\ below_a_fact y fl p t.

Theorem fmt_fp_facts_gen : forall d prec, dfin d -> 1 <= prec <= 26 -> fmt_fp_facts (f128_of_d d) 0 prec CHR_g.
Proof.
  intros d prec Hfin Hp.
  pose proof (yn_widened d Hfin) as [YN0 YN1].
  destruct (fmt_loops d prec CHR_g Hfin ltac:(lia) ltac:(cbv; discriminate))
    as [nz [fr [e0 [y2 (C1 & C2 & C3 & C4 & REST)]]]].
  cbv zeta in REST. destruct REST as (He2 & [big [z (ED & Hz & WB & LB & ZO & W0 & ZC & [s1 (EU & HS1 & DS1 & ZS1 & [big2 [a2 [z2 (EDN & PN & PZ)]]])])]]).
  set (y := f128_of_d d) in *.
  set (e2 := if nz then e0 - 1 - 28 else e0) in *.
  replace (if nz then (if nz then e0 - 1 else e0) - 28 else if nz then e0 - 1 else e0) with e2 in * by (subst e2; destruct nz; reflexivity).
  set (yy := if nz then f128_mul y2 (f128_of_d D_0x1p28) else y2) in *.
  set (r0 := if e2 <? 0 then 0 else 122) in *.
  replace (prec <? 0) with false in * by (symmetry; apply Z.ltb_ge; lia).

  assert (PRE : forall y1 fr' e0', fst (fst (ffp_sign y 0)) = y1 -> frexpl FREXPL_FUEL y1 0 = Some (fr', e0') -> fr' = fr /\ e0' = e0).
  { intros y1 fr' e0' <- E. rewrite ffp_sign_fst, C2 in E. injection E as <- <-. split; reflexivity. }
  assert (YE : forall y' e2', (y' = (if negb (f128_le (f128_mul fr (f128_of_i32 2)) F128_ZERO =? 0) then f128_mul (f128_mul fr (f128_of_i32 2)) (f128_of_d D_0x1p28) else f128_mul fr (f128_of_i32 2))
            /\ e2' = (if negb (f128_le (f128_mul fr (f128_of_i32 2)) F128_ZERO =? 0) then e0 - 1 - 28 else e0)) -> y' = yy /\ e2' = e2).
  { intros y' e2' [-> ->]. rewrite C3, C4. split; reflexivity. }

  assert (RUN : forall p1 r0' bigD aD zD, run_to_dn y 0 prec CHR_g p1 r0' bigD aD zD -> p1 = prec /\ r0' = r0 /\ bigD = big2 /\ aD = a2 /\ zD = z2).
  { intros p1 r0' bigD aD zD (y1 & fr' & e0' & y' & e2' & b' & z' & yf & s & e2f & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
    destruct (PRE _ _ _ S1 S2) as [-> ->]. destruct (YE _ _ S3) as [-> ->].
    replace (prec <? 0) with false in S4 by (symmetry; apply Z.ltb_ge; lia). subst p1 r0'. fold r0 in S6, S7, S8.
    rewrite ED in S6. injection S6 as <- <- <-. rewrite EU in S7. injection S7 as <-. rewrite EDN in S8. injection S8 as <- <- <- _.
    repeat split; reflexivity. }
  unfold fmt_fp_facts. fold y.
  split; [exact YN0|]. split; [exact YN1|].
  split. {
    intros y1 fr' e0' y' e2' b' z' y'' S1 S2 S3 S4.
    destruct (PRE _ _ _ S1 S2) as [-> ->]. destruct (YE _ _ S3) as [-> ->]. fold r0 in S4 |- *.
    rewrite ED in S4. injection S4 as <- <- <-. lia. }
  split. {
    intros y1 fr' e0' S1 S2. destruct (PRE _ _ _ S1 S2) as [-> ->]. cbv zeta. rewrite C3, C4. lia. }
  split. {
    intros y1 fr' e0' y' e2' b' z' y'' s S1 S2 S3 S4 S5.
    destruct (PRE _ _ _ S1 S2) as [-> ->]. destruct (YE _ _ S3) as [-> ->]. fold r0 in S4, S5 |- *.
    rewrite ED in S4. injection S4 as <- <- <-. rewrite EU in S5. injection S5 as <-.
    intros n bigI aI zI e2I IT HeI. rewrite fmt_fp_dn_iter_eq in IT.
    replace (if prec <? 0 then 6 else prec) with prec in IT by (replace (prec <? 0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    destruct (Z.lt_ge_cases e2 0) as [NEG|NNEG].
    - destruct nz; [| destruct (ZC eq_refl) as [E0 _]; lia].
      pose proof (DS1 eq_refl NEG) as DI. rewrite (HS1 ltac:(lia)) in DI, IT.
      assert (R0 : r0 = 0) by (subst r0; replace (e2 <? 0) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      rewrite R0 in IT, DI.
      pose proof (dn_iter_DNI prec CHR_g n _ _ ltac:(lia) ltac:(cbv; discriminate) DI IT) as (_ & _ & AZ & NZ' & _ & ZM & _).
      unfold dn_ok. unfold dnm in ZM. split; [lia|]. intros; lia.
    - destruct (ZS1 NNEG) as [b1 [a1 [z1 ES1]]]. rewrite ES1 in IT. destruct n as [|n].
      + cbn in IT. injection IT as <- <- <- <-. lia.
      + cbn [dn_iter] in IT. change (0 <? 0) with false in IT. discriminate IT. }
  split. {
    intros p1 r0' bigD aD zD R i. destruct (RUN _ _ _ _ _ R) as (-> & -> & -> & -> & ->).
    destruct nz.
    - destruct (PN eq_refl) as (W & _). unfold W9, NB in W. apply W.
    - destruct (PZ eq_refl) as (-> & _). rewrite znth_zrepeat. destruct (_ && _); lia. }
  split. {
    intros p1 r0' bigD aD zD R e prefix pl bigR aR zR eR Ee ER. destruct (RUN _ _ _ _ _ R) as (-> & -> & -> & -> & ->).
    rewrite ffp_e_eq in Ee. rewrite ffp_R_eq, ffp_j_eq in ER.
    destruct nz.
    - pose proof (PN eq_refl) as PO. destruct (g_e_spec r0 big2 a2 z2 PO) as [e' (Ee' & TSe)]. rewrite Ee' in Ee. injection Ee as ->.
      pose proof PO as (_ & _ & _ & _ & NZa & _ & Rr).
      destruct (R_spec_gen prec prefix pl r0 big2 a2 z2 e TSe NZa) as [bigR' [aR' [zR' [eR' (ER' & TSR & _)]]]]; [| | lia |].
      { intros R0. destruct Rr as [[_ B]|[R1 _]]; [exact B| lia]. }
      { intros R1. destruct Rr as [[R0 _]|(_ & B & _)]; [lia| lia]. }
      rewrite ER' in ER. injection ER as <- <- <- <-. destruct TSR as (_ & _ & AZ & _). lia.
    - destruct (PZ eq_refl) as (-> & -> & ->). destruct (ZC eq_refl) as (E20 & _ & _).
      assert (R0 : r0 = 122) by (subst r0; rewrite E20; reflexivity). rewrite R0 in *.
      assert (EE : e = 0). { revert Ee. clear. intros Ee. vm_compute in Ee. congruence. }
      subst e. unfold g_R in ER.
      replace (g_j CHR_g prec 0 <? 9 * (123 - 122 - 1)) with false in ER.
      2:{ symmetry. apply Z.ltb_ge. unfold g_j. change (Z.lor CHR_g 32 =? CHR_f) with false. change (Z.lor CHR_g 32 =? CHR_g) with true.
          replace (prec =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb]. lia. }
      injection ER as <- <- <- <-. lia. }
  split. {
    intros p1 r0' bigD aD zD R e prefix pl bigR aR zR eR zS Ee ER ES Ht HzS. destruct (RUN _ _ _ _ _ R) as (-> & -> & -> & -> & ->).
    rewrite ffp_e_eq in Ee. rewrite ffp_R_eq, ffp_j_eq in ER.
    destruct nz.
    - pose proof (PN eq_refl) as PO. destruct (g_e_spec r0 big2 a2 z2 PO) as [e' (Ee' & TSe)]. rewrite Ee' in Ee. injection Ee as ->.
      pose proof PO as (_ & _ & _ & _ & NZa & _ & Rr).
      destruct (R_spec_gen prec prefix pl r0 big2 a2 z2 e TSe NZa) as [bigR' [aR' [zR' [eR' (ER' & TSR & NZR & _)]]]]; [| | lia |].
      { intros R0. destruct Rr as [[_ B]|[R1 _]]; [exact B| lia]. }
      { intros R1. destruct Rr as [[R0 _]|(_ & B & _)]; [lia| lia]. }
      rewrite ER' in ER. injection ER as <- <- <- <-. destruct TSR as (_ & _ & AZ & Z7 & _).
      destruct (strip_spec bigR' aR' zR' ltac:(lia) ltac:(lia) NZR) as [zS' (ES' & HzS' & _)]. rewrite ES' in ES. injection ES as <-. lia.
    - destruct (PZ eq_refl) as (-> & -> & ->). destruct (ZC eq_refl) as (E20 & _ & _).
      assert (R0 : r0 = 122) by (subst r0; rewrite E20; reflexivity). rewrite R0 in *.
      assert (EE : e = 0). { revert Ee. clear. intros Ee. vm_compute in Ee. congruence. }
      subst e. unfold g_R in ER.
      replace (g_j CHR_g prec 0 <? 9 * (123 - 122 - 1)) with false in ER.
      2:{ symmetry. apply Z.ltb_ge. unfold g_j. change (Z.lor CHR_g 32 =? CHR_f) with false. change (Z.lor CHR_g 32 =? CHR_g) with true.
          replace (prec =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb]. lia. }
      injection ER as <- <- <- <-. reflexivity. }

  intros p1 r0' bigD aD zD R k Hk. destruct (RUN _ _ _ _ _ R) as (-> & -> & -> & -> & ->).
  destruct nz.
  - destruct (PN eq_refl) as (_ & _ & _ & _ & _ & ZB & _). apply ZB. lia.
  - destruct (PZ eq_refl) as (-> & _). rewrite znth_zrepeat. destruct (_ && _); lia.
Qed.
