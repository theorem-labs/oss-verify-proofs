(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F5 Require Import FmtFp_split.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Notation "'let?' x ':=' e 'in' k" :=
  (match e with Some x => k | None => None end)
  (at level 200, x pattern, e at level 100, k at level 200, only parsing).

Definition ffp_gadj (fl t p : Z) (big : list Z) (a r z e : Z) : option (Z * Z) :=
  if Z.lor t 32 =? CHR_g then
    let p := if p =? 0 then p + 1 else p in
    let '(t, p) := if (e <? p) && (-4 <=? e) then (t - 1, p - (e + 1)) else (t - 2, p - 1) in
    if Z.land fl ALT_FORM =? 0 then
      let? j := if (a <? z) && negb (znth big (z - 1) =? 0)
                then (let? (i, j) := fmt_fp_tz TEN_FUEL (znth big (z - 1)) (10, 0) in Some j)
                else Some 9 in
      let p := if Z.lor t 32 =? CHR_f
               then Z.min p (Z.max 0 (9 * (z - r - 1) - j))
               else Z.min p (Z.max 0 (9 * (z - r - 1) + e - j)) in
      Some (p, t)
    else Some (p, t)
  else Some (p, t).

Definition ffp_gadj2 (fl t p : Z) (big : list Z) (a r z e : Z) : option (Z * Z) :=
  if Z.land fl ALT_FORM =? 0 then
    let? j := if (a <? z) && negb (znth big (z - 1) =? 0)
              then (let? (i, j) := fmt_fp_tz TEN_FUEL (znth big (z - 1)) (10, 0) in Some j)
              else Some 9 in
    let p := if Z.lor t 32 =? CHR_f
             then Z.min p (Z.max 0 (9 * (z - r - 1) - j))
             else Z.min p (Z.max 0 (9 * (z - r - 1) + e - j)) in
    Some (p, t)
  else Some (p, t).

Definition gadj_cond (p e : Z) : bool := ((e <? (if p =? 0 then p + 1 else p)) && (-4 <=? e))%Z.

Lemma ffp_gadj_eq : forall fl t p big a r z e,
  ffp_gadj fl t p big a r z e =
    (if Z.lor t 32 =? CHR_g then
       let p' := if p =? 0 then p + 1 else p in
       ffp_gadj2 fl (if gadj_cond p e then t - 1 else t - 2) (if gadj_cond p e then p' - (e + 1) else p' - 1) big a r z e
     else Some (p, t)).
Proof.
  intros. unfold ffp_gadj, ffp_gadj2, gadj_cond. destruct (Z.lor t 32 =? CHR_g); [|reflexivity].
  cbv zeta. destruct ((e <? (if p =? 0 then p + 1 else p)) && (-4 <=? e)); reflexivity.
Qed.

Definition ffp_H6 (o : list Z) (w fl pl l : Z) : option (list Z * Z) :=
  let? o := pad o CHR_sp w (pl + l) (Z.lxor fl LEFT_ADJ) in
  Some (o, Z.max w (pl + l)).

Definition ffp_H5 (o : list Z) (w fl t p pl : Z) (big : list Z) (a r z l : Z) (ebuf0 : list Z) (estr : Z) : option (list Z * Z) :=
  let? o := if Z.lor t 32 =? CHR_f
            then fmt_fp_emit_f o big a r z p fl
            else fmt_fp_emit_e o big a z p fl ebuf0 estr in
  ffp_H6 o w fl pl l.

Definition ffp_H4 (o : list Z) (w fl t p prefix pl : Z) (big : list Z) (a r z l : Z) (ebuf0 : list Z) (estr : Z) : option (list Z * Z) :=
  if INT_MAX - pl <? l then Some (o, -1) else
  let? o := pad o CHR_sp w (pl + l) fl in
  let o := out o (zsub PREFIX_STR prefix pl) in
  let? o := pad o CHR_0 w (pl + l) (Z.lxor fl ZERO_PAD) in
  ffp_H5 o w fl t p pl big a r z l ebuf0 estr.

Definition ffp_H3 (o : list Z) (w fl t p prefix pl : Z) (big : list Z) (a r z e : Z) : option (list Z * Z) :=
  let palt := if negb (p =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0 in
  if INT_MAX - 1 - palt <? p then Some (o, -1) else
  let l := 1 + p + palt in
  let? len := fmt_fp_len t l e in
  match len with
  | Ret v => Some (o, v)
  | Cont (l, ebuf0, estr) => ffp_H4 o w fl t p prefix pl big a r z l ebuf0 estr
  end.

Definition ffp_H2 (o : list Z) (w fl t p prefix pl : Z) (big : list Z) (a r z e : Z) : option (list Z * Z) :=
  let? (p, t) := ffp_gadj fl t p big a r z e in
  ffp_H3 o w fl t p prefix pl big a r z e.

Lemma ffp_H_eq : forall o w fl t p prefix pl big a r z e,
  ffp_H o w fl t p prefix pl big a r z e =
    (let? z := fmt_fp_strip BIG_FUEL big a z in ffp_H2 o w fl t p prefix pl big a r z e).
Proof.
  intros. unfold ffp_H, ffp_H2, ffp_gadj, ffp_H3, ffp_H4, ffp_H5, ffp_H6.
  destruct (fmt_fp_strip BIG_FUEL big a z) as [zS|]; [|reflexivity].
  destruct (Z.lor t 32 =? CHR_g); [|reflexivity].
  destruct ((e <? (if p =? 0 then p + 1 else p)) && (-4 <=? e)); destruct (Z.land fl ALT_FORM =? 0); reflexivity.
Qed.

Definition ffp_F2 (o : list Z) (big : list Z) (z p fl d : Z) : option (list Z) :=
  let o := if negb (p =? 0) || negb (Z.land fl ALT_FORM =? 0) then out o [CHR_dot] else o in
  let? (d, p, o) := fmt_fp_ffrac BIG_FUEL big z (d, p, o) in
  pad o CHR_0 (p + 9) 9 0.

Lemma fmt_fp_emit_f_eq : forall o big a r z p fl,
  fmt_fp_emit_f o big a r z p fl =
    (let a := if r <? a then r else a in
     let? (d, o) := fmt_fp_fint BIG_FUEL big a r (a, o) in
     ffp_F2 o big z p fl d).
Proof. reflexivity. Qed.

Definition ffp_E2 (o : list Z) (p : Z) (ebuf0 : list Z) (estr : Z) : option (list Z) :=
  let? o := pad o CHR_0 (p + 18) 18 0 in
  Some (out o (zsub ebuf0 estr (12 - estr))).

Lemma fmt_fp_emit_e_eq : forall o big a z p fl ebuf0 estr,
  fmt_fp_emit_e o big a z p fl ebuf0 estr =
    (let z := if z <=? a then a + 1 else z in
     let? (d, p, o) := fmt_fp_eloop BIG_FUEL big a z fl (a, p, o) in
     ffp_E2 o p ebuf0 estr).
Proof. reflexivity. Qed.

Lemma fmt_fp_tz_step : forall k v i j,
  fmt_fp_tz (S k) v (i, j) = (if v mod i =? 0 then fmt_fp_tz k v (i * 10, j + 1) else Some (i, j)).
Proof. reflexivity. Qed.

Lemma fmt_fp_fint_step : forall k big a r d o,
  fmt_fp_fint (S k) big a r (d, o) =
    (if d <=? r then (let? st := fmt_fp_fint_body big a (d, o) in fmt_fp_fint k big a r st) else Some (d, o)).
Proof. reflexivity. Qed.

Lemma fmt_fp_ffrac_step : forall k big z d p o,
  fmt_fp_ffrac (S k) big z (d, p, o) =
    (if (d <? z) && (0 <? p) then (let? st := fmt_fp_ffrac_body big (d, p, o) in fmt_fp_ffrac k big z st) else Some (d, p, o)).
Proof. reflexivity. Qed.

Lemma fmt_fp_eloop_step : forall k big a z fl d p o,
  fmt_fp_eloop (S k) big a z fl (d, p, o) =
    (if (d <? z) && (0 <=? p) then (let? st := fmt_fp_eloop_body big a fl (d, p, o) in fmt_fp_eloop k big a z fl st) else Some (d, p, o)).
Proof. reflexivity. Qed.

Lemma fmt_fp_zfill_step : forall k s buf,
  fmt_fp_zfill (S k) (s, buf) = (if 0 <? s then fmt_fp_zfill k (s - 1, zupd buf (s - 1) CHR_0) else Some (s, buf)).
Proof. reflexivity. Qed.

Lemma fmt_fp_epad_step : forall k estr ebuf0,
  fmt_fp_epad (S k) (estr, ebuf0) = (if 12 - estr <? 2 then fmt_fp_epad k (estr - 1, zupd ebuf0 (estr - 1) CHR_0) else Some (estr, ebuf0)).
Proof. reflexivity. Qed.

Lemma fmt_u_loop_step : forall k y s b,
  fmt_u_loop (S k) (y, s, b) = (if negb (y =? 0) then fmt_u_loop k (y / 10, s - 1, zupd b (s - 1) (CHR_0 + y mod 10)) else Some (y, s, b)).
Proof. reflexivity. Qed.

Fixpoint ndig_fuel (k : nat) (x : Z) : Z :=
  match k with O => 0 | S k' => if x =? 0 then 0 else 1 + ndig_fuel k' (x / 10) end.
Definition ndig (x : Z) : Z := ndig_fuel 21 x.

Lemma ndig_fuel_nonneg : forall k x, 0 <= ndig_fuel k x.
Proof. induction k as [|k IH]; intros x; cbn [ndig_fuel]; [lia|]. destruct (x =? 0); [lia|]. pose proof (IH (x / 10)). lia. Qed.

Lemma fmt_u_loop_res : forall k y s b y' s' b',
  fmt_u_loop k (y, s, b) = Some (y', s', b') -> 0 <= y ->
  y' = 0 /\ s' = s - ndig_fuel k y /\ length b' = length b
  /\ (forall i, (i < s' \/ s <= i) -> znth b' i = znth b i)
  /\ (forall i, s' <= i < s -> 0 <= i < zlength b -> znth b' i = CHR_0 + (y / 10 ^ (s - 1 - i)) mod 10).
Proof.
  induction k as [|k IH]; intros y s b y' s' b' H Hy; [discriminate H|].
  rewrite fmt_u_loop_step in H. cbn [ndig_fuel]. destruct (Z.eqb_spec y 0) as [->|Hne].
  - cbn in H. injection H as <- <- <-. split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
    split; [intros; reflexivity | intros; lia].
  - cbn [negb] in H. apply IH in H; [|apply Z.div_pos; lia]. destruct H as (H1 & H2 & H3 & H4 & H5).
    split; [exact H1|]. split; [lia|]. split; [rewrite H3; apply zupd_length|]. split.
    + intros i Hi. pose proof (ndig_fuel_nonneg k (y / 10)). rewrite H4 by lia. apply znth_zupd_neq. lia.
    + intros i Hi Hib. destruct (Z.eq_dec i (s - 1)) as [->|Hne2].
      * rewrite H4 by lia. rewrite znth_zupd_eq by lia. replace (s - 1 - (s - 1)) with 0 by lia.
        change (10 ^ 0) with 1. rewrite Z.div_1_r. reflexivity.
      * rewrite H5 by (unfold zlength in *; rewrite ?zupd_length; lia).
        rewrite Z.div_div by lia. replace (10 * 10 ^ (s - 1 - 1 - i)) with (10 ^ (s - 1 - i)); [reflexivity|].
        replace (s - 1 - i) with (Z.succ (s - 1 - 1 - i)) by lia. rewrite Z.pow_succ_r by lia. reflexivity.
Qed.

Lemma fmt_fp_strip_step' : forall k big a z,
  fmt_fp_strip (S k) big a z = (if (a <? z) && (znth big (z - 1) =? 0) then fmt_fp_strip k big a (z - 1) else Some z).
Proof. reflexivity. Qed.

Lemma fmt_fp_strip_last : forall k big a z z', fmt_fp_strip k big a z = Some z' -> a < z' -> znth big (z' - 1) <> 0.
Proof.
  induction k as [|k IH]; intros big a z z' H Hlt; [discriminate H|].
  rewrite fmt_fp_strip_step' in H. destruct (Z.ltb_spec0 a z); cbn [andb] in H.
  - destruct (Z.eqb_spec (znth big (z - 1)) 0); [exact (IH _ _ _ _ H Hlt)|]. injection H as <-. assumption.
  - injection H as <-. lia.
Qed.

Lemma ndig_fuel_le : forall k x n, 0 <= x -> 0 <= n -> x < 10 ^ n -> ndig_fuel k x <= n.
Proof.
  induction k as [|k IH]; intros x n Hx Hn Hlt; cbn [ndig_fuel]; [lia|].
  destruct (Z.eqb_spec x 0); [lia|].
  assert (1 <= n). { destruct (Z.le_gt_cases 1 n); [assumption|]. replace n with 0 in Hlt by lia. change (10^0) with 1 in Hlt. lia. }
  assert (x / 10 < 10 ^ (n - 1)).
  { apply Z.div_lt_upper_bound; [lia|]. replace (10 * 10 ^ (n - 1)) with (10 ^ n); [exact Hlt|].
    replace n with (Z.succ (n - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
  pose proof (IH (x / 10) (n - 1) ltac:(apply Z.div_pos; lia) ltac:(lia) H0). lia.
Qed.

Lemma ndig_fuel_pos : forall k x, 0 < x -> (0 < k)%nat -> 1 <= ndig_fuel k x.
Proof. intros k x Hx Hk. destruct k; [lia|]. cbn [ndig_fuel]. destruct (Z.eqb_spec x 0); [lia|]. pose proof (ndig_fuel_nonneg k (x / 10)). lia. Qed.

Lemma fmt_fp_epad_res : forall s b, 2 <= s <= 12 ->
  fmt_fp_epad EPAD_FUEL (s, b) =
    Some (Z.min s 10, if s =? 12 then zupd (zupd b 11 CHR_0) 10 CHR_0 else if s =? 11 then zupd b 10 CHR_0 else b).
Proof.
  intros s b Hs. unfold EPAD_FUEL. rewrite fmt_fp_epad_step.
  destruct (Z.ltb_spec0 (12 - s) 2).
  - rewrite fmt_fp_epad_step. destruct (Z.ltb_spec0 (12 - (s - 1)) 2).
    + rewrite fmt_fp_epad_step. destruct (Z.ltb_spec0 (12 - (s - 1 - 1)) 2); [lia|].
      replace s with 12 by lia. reflexivity.
    + replace s with 11 by lia. reflexivity.
  - rewrite (proj2 (Z.eqb_neq s 12)) by lia. rewrite (proj2 (Z.eqb_neq s 11)) by lia. f_equal. f_equal. lia.
Qed.

Definition extends (o o' : list Z) : Prop := exists sfx, o' = o ++ sfx.
Lemma extends_refl : forall o, extends o o.
Proof. intros o. exists []. rewrite app_nil_r. reflexivity. Qed.
Lemma extends_trans : forall o1 o2 o3, extends o1 o2 -> extends o2 o3 -> extends o1 o3.
Proof. intros o1 o2 o3 [s1 ->] [s2 ->]. exists (s1 ++ s2). rewrite app_assoc. reflexivity. Qed.
Lemma extends_out : forall o bs, extends o (out o bs).
Proof. intros. exists bs. reflexivity. Qed.
Lemma extends_length : forall o o', extends o o' -> (length o <= length o')%nat.
Proof. intros o o' [s ->]. rewrite app_length. lia. Qed.

Lemma pad_loop_extends : forall c k l o l' o', pad_loop c k (l, o) = Some (l', o') -> extends o o'.
Proof.
  induction k as [|k IH]; intros l o l' o' H; [discriminate H|].
  cbn [pad_loop] in H. destruct (256 <=? l).
  - cbn [pad_loop_body] in H. apply IH in H. eapply extends_trans; [apply extends_out | exact H].
  - injection H as <- <-. apply extends_refl.
Qed.
Lemma pad_extends : forall o c w l fl o', pad o c w l fl = Some o' -> extends o o'.
Proof.
  intros o c w l fl o' H. unfold pad in H. destruct (negb _ || _).
  - injection H as <-. apply extends_refl.
  - destruct (pad_loop c PAD_FUEL (w - l, o)) as [[l1 o1]|] eqn:E; [|discriminate H]. injection H as <-.
    eapply extends_trans; [eapply pad_loop_extends; exact E | apply extends_out].
Qed.
Lemma fint_extends : forall k big a r d o d' o', fmt_fp_fint k big a r (d, o) = Some (d', o') -> extends o o'.
Proof.
  induction k as [|k IH]; intros big a r d o d' o' H; [discriminate H|].
  rewrite fmt_fp_fint_step in H. destruct (d <=? r).
  - unfold fmt_fp_fint_body in H. destruct (fmt_u (znth big d) (zrepeat 0 37) 9) as [[s b]|]; [|discriminate H].
    destruct (if negb (d =? a) then _ else _) as [[s1 b1]|]; [|discriminate H].
    apply IH in H. eapply extends_trans; [apply extends_out | exact H].
  - injection H as <- <-. apply extends_refl.
Qed.
Lemma ffrac_extends : forall k big z d p o d' p' o', fmt_fp_ffrac k big z (d, p, o) = Some (d', p', o') -> extends o o'.
Proof.
  induction k as [|k IH]; intros big z d p o d' p' o' H; [discriminate H|].
  rewrite fmt_fp_ffrac_step in H. destruct ((d <? z) && (0 <? p)).
  - unfold fmt_fp_ffrac_body in H. destruct (fmt_u (znth big d) (zrepeat 0 37) 9) as [[s b]|]; [|discriminate H].
    destruct (fmt_fp_zfill ZFILL_FUEL (s, b)) as [[s1 b1]|]; [|discriminate H].
    apply IH in H. eapply extends_trans; [apply extends_out | exact H].
  - injection H as <- <- <-. apply extends_refl.
Qed.
Lemma eloop_extends : forall k big a z fl d p o d' p' o', fmt_fp_eloop k big a z fl (d, p, o) = Some (d', p', o') -> extends o o'.
Proof.
  induction k as [|k IH]; intros big a z fl d p o d' p' o' H; [discriminate H|].
  rewrite fmt_fp_eloop_step in H. destruct ((d <? z) && (0 <=? p)).
  - unfold fmt_fp_eloop_body in H. destruct (fmt_u (znth big d) (zrepeat 0 37) 9) as [[s b]|]; [|discriminate H].
    destruct (if s =? 9 then _ else _) as [s1 b1].
    destruct (negb (d =? a)).
    + destruct (fmt_fp_zfill ZFILL_FUEL (s1, b1)) as [[s2 b2]|]; [|discriminate H].
      apply IH in H. eapply extends_trans; [apply extends_out | exact H].
    + apply IH in H. eapply extends_trans; [|exact H].
      eapply extends_trans; [|apply extends_out]. eapply extends_trans; [apply extends_out|].
      destruct ((0 <? p) || negb (Z.land fl ALT_FORM =? 0)); [apply extends_out | apply extends_refl].
  - injection H as <- <- <-. apply extends_refl.
Qed.
Lemma emit_f_extends : forall o big a r z p fl o', fmt_fp_emit_f o big a r z p fl = Some o' -> extends o o'.
Proof.
  intros o big a r z p fl o' H. unfold fmt_fp_emit_f in H.
  destruct (fmt_fp_fint BIG_FUEL big _ r _) as [[d o2]|] eqn:E1; [|discriminate H].
  destruct (fmt_fp_ffrac BIG_FUEL big z _) as [[[d3 p3] o3]|] eqn:E2; [|discriminate H].
  apply fint_extends in E1. apply ffrac_extends in E2. apply pad_extends in H.
  eapply extends_trans; [exact E1|]. eapply extends_trans; [|eapply extends_trans; [exact E2 | exact H]].
  destruct (negb (p =? 0) || negb (Z.land fl ALT_FORM =? 0)); [apply extends_out | apply extends_refl].
Qed.
Lemma emit_e_extends : forall o big a z p fl ebuf0 estr o', fmt_fp_emit_e o big a z p fl ebuf0 estr = Some o' -> extends o o'.
Proof.
  intros o big a z p fl ebuf0 estr o' H. unfold fmt_fp_emit_e in H.
  destruct (fmt_fp_eloop BIG_FUEL big a _ fl _) as [[[d2 p2] o2]|] eqn:E1; [|discriminate H].
  destruct (pad o2 CHR_0 (p2 + 18) 18 0) as [o3|] eqn:E2; [|discriminate H]. injection H as <-.
  apply eloop_extends in E1. apply pad_extends in E2.
  eapply extends_trans; [exact E1|]. eapply extends_trans; [exact E2 | apply extends_out].
Qed.
Lemma H6_extends : forall o w fl pl l o1 ret, ffp_H6 o w fl pl l = Some (o1, ret) -> extends o o1.
Proof.
  intros o w fl pl l o1 ret H. unfold ffp_H6 in H. destruct (pad o CHR_sp w (pl + l) _) as [o2|] eqn:E; [|discriminate H].
  injection H as <- _. eapply pad_extends. exact E.
Qed.
Lemma H5_extends : forall o w fl t p pl big a r z l ebuf0 estr o1 ret,
  ffp_H5 o w fl t p pl big a r z l ebuf0 estr = Some (o1, ret) -> extends o o1.
Proof.
  intros until ret. intros H. unfold ffp_H5 in H.
  destruct (if Z.lor t 32 =? CHR_f then _ else _) as [o2|] eqn:E; [|discriminate H].
  eapply extends_trans; [|eapply H6_extends; exact H].
  destruct (Z.lor t 32 =? CHR_f); [eapply emit_f_extends | eapply emit_e_extends]; exact E.
Qed.

Lemma fmt_fp_zfill_res : forall k s b, 0 <= s -> (Z.to_nat s < k)%nat ->
  exists b', fmt_fp_zfill k (s, b) = Some (0, b') /\ length b' = length b
    /\ (forall i, 0 <= i < s -> i < zlength b -> znth b' i = CHR_0)
    /\ (forall i, s <= i -> znth b' i = znth b i).
Proof.
  induction k as [|k IH]; intros s b Hs Hk; [lia|].
  rewrite fmt_fp_zfill_step. destruct (Z.ltb_spec0 0 s).
  - destruct (IH (s - 1) (zupd b (s - 1) CHR_0) ltac:(lia) ltac:(lia)) as (b' & H1 & H2 & H3 & H4).
    exists b'. split; [exact H1|]. split; [rewrite H2; apply zupd_length|]. split.
    + intros i Hi Hl. destruct (Z.eq_dec i (s - 1)) as [->|Hne].
      * rewrite H4 by lia. apply znth_zupd_eq. lia.
      * apply H3; [lia|]. unfold zlength in *. rewrite zupd_length. lia.
    + intros i Hi. rewrite H4 by lia. apply znth_zupd_neq. lia.
  - exists b. replace s with 0 by lia. split; [reflexivity|]. split; [reflexivity|]. split; [intros; lia | intros; reflexivity].
Qed.

Lemma pad_loop_len : forall c k l o l' o', pad_loop c k (l, o) = Some (l', o') -> 0 <= l ->
  (length o' + Z.to_nat l' = length o + Z.to_nat l)%nat /\ 0 <= l' < 256.
Proof.
  induction k as [|k IH]; intros l o l' o' H Hl; [discriminate H|].
  cbn [pad_loop] in H. destruct (Z.leb_spec0 256 l).
  - cbn [pad_loop_body] in H. apply IH in H; [|lia]. destruct H as [H1 H2].
    unfold out in H1. rewrite app_length in H1. unfold zrepeat in H1. rewrite repeat_length in H1. split; [lia|lia].
  - injection H as <- <-. split; [reflexivity|lia].
Qed.
Lemma pad_length : forall o c w l fl o', pad o c w l fl = Some o' ->
  length o' = (length o + (if (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%Z then 0%nat else Z.to_nat (w - l)))%nat.
Proof.
  intros o c w l fl o' H. unfold pad in H.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%Z eqn:E.
  - injection H as <-. lia.
  - destruct (pad_loop c PAD_FUEL (w - l, o)) as [[l1 o1]|] eqn:EL; [|discriminate H]. injection H as <-.
    apply Bool.orb_false_iff in E. destruct E as [_ E]. apply Z.leb_gt in E.
    apply pad_loop_len in EL; [|lia]. destruct EL as [H1 H2].
    unfold out. rewrite app_length. unfold zrepeat. rewrite repeat_length. lia.
Qed.
