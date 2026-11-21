(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import Prog ZIface InflateState Inftrees ModelRel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ItCovBits ItCovPre ItCovMath.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition fill_hits (base incr q x : Z) : bool :=
  (base <=? x) && (x <? base + q * incr) && ((x - base) mod incr =? 0).

Definition fill_body (here incr huff drop next : Z) (ft : Z * arr) : bool * (Z * arr) :=
  let '(fill, tbl) := ft in
  let fill := wrap32 (fill - incr) in
  let tbl := arr_set tbl (next + (Z.shiftr huff drop + fill)) here in
  if negb (fill =? 0) then (true, (fill, tbl)) else (false, (fill, tbl)).

Lemma it_fill_eq : forall here incr huff drop next fill tbl,
  it_fill here incr huff drop next fill tbl = snd (loopZ fill (fill_body here incr huff drop next) (fill, tbl)).
Proof. reflexivity. Qed.

Lemma fill_body_eq : forall here incr huff drop next f (t : arr),
  fill_body here incr huff drop next (f, t) =
  (negb (wrap32 (f - incr) =? 0), (wrap32 (f - incr), arr_set t (next + (Z.shiftr huff drop + wrap32 (f - incr))) here)).
Proof. intros. unfold fill_body. destruct (negb (wrap32 (f - incr) =? 0)); reflexivity. Qed.

Lemma fill_hits_false_lo : forall base incr q x, x < base -> fill_hits base incr q x = false.
Proof. intros. unfold fill_hits. destruct (Z.leb_spec base x); [lia|reflexivity]. Qed.

Lemma it_fill_loop : forall here incr huff drop next (tbl : arr) (r : nat) (n : Z) (t : arr),
  0 < incr -> (1 <= r)%nat -> Z.of_nat r * incr < 2 ^ 32 -> Z.of_nat r <= n ->
  arr_len t = arr_len tbl ->
  let h := Z.shiftr huff drop in
  let res := snd (loopZ n (fill_body here incr huff drop next) (Z.of_nat r * incr, t)) in
  arr_len res = arr_len tbl /\
  forall x, arr_get res x =
    if fill_hits (next + h) incr (Z.of_nat r) x && arr_inb tbl x then here else arr_get t x.
Proof.
  intros here incr huff drop next tbl r. induction r as [|r IH]; intros n t Hincr Hr1 Hr Hn Hlen; [lia|]; cbv zeta.
  rewrite loopZ_step by lia. rewrite fill_body_eq.
  assert (W : wrap32 (Z.of_nat (S r) * incr - incr) = Z.of_nat r * incr).
  { replace (Z.of_nat (S r) * incr - incr) with (Z.of_nat r * incr) by lia. apply wrap32_id. nia. }
  rewrite !W.
  destruct (Nat.eq_dec r 0) as [->|Hr0].
  -
    replace (Z.of_nat 0 * incr) with 0 by lia. cbn [Z.eqb negb snd]. split; [rewrite arr_len_set; exact Hlen|].
    intros x. rewrite arr_get_set. unfold arr_inb. rewrite Hlen.
    unfold fill_hits. change (Z.of_nat 1 * incr) with (1 * incr)%Z.
    destruct (Z.eqb_spec (next + (Z.shiftr huff drop + 0)) x) as [E|E].
    + subst x. replace (next + (Z.shiftr huff drop + 0) - (next + Z.shiftr huff drop)) with 0 by lia.
      rewrite Z.mod_0_l by lia. cbn [Z.eqb].
      replace (next + Z.shiftr huff drop <=? next + (Z.shiftr huff drop + 0)) with true by (symmetry; apply Z.leb_le; lia).
      replace (next + (Z.shiftr huff drop + 0) <? next + Z.shiftr huff drop + 1 * incr) with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [andb]. reflexivity.
    + cbn [andb].
      destruct (Z.leb_spec (next + Z.shiftr huff drop) x); cbn [andb]; [|reflexivity].
      destruct (Z.ltb_spec x (next + Z.shiftr huff drop + 1 * incr)); cbn [andb]; [|reflexivity].
      destruct (Z.eqb_spec ((x - (next + Z.shiftr huff drop)) mod incr) 0); cbn [andb]; [|reflexivity].
      exfalso. apply E. pose proof (Z.div_mod (x - (next + Z.shiftr huff drop)) incr ltac:(lia)) as DM.
      assert ((x - (next + Z.shiftr huff drop)) / incr = 0) by (apply Z.div_small; lia). lia.
  -
    assert (NZ : negb (Z.of_nat r * incr =? 0) = true).
    { apply negb_true_iff. apply Z.eqb_neq. nia. }
    rewrite NZ.
    destruct (IH (n - 1) (arr_set t (next + (Z.shiftr huff drop + Z.of_nat r * incr)) here) Hincr ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(rewrite arr_len_set; exact Hlen)) as [A Bx].
    split; [exact A|]. intros x. rewrite Bx. rewrite arr_get_set. unfold arr_inb. rewrite Hlen.
    unfold fill_hits.
    destruct (Z.eqb_spec (next + (Z.shiftr huff drop + Z.of_nat r * incr)) x) as [E|E].
    + subst x.
      replace (next + (Z.shiftr huff drop + Z.of_nat r * incr) - (next + Z.shiftr huff drop)) with (Z.of_nat r * incr) by lia.
      rewrite Z.mod_mul by lia. cbn [Z.eqb].
      replace (next + Z.shiftr huff drop <=? next + (Z.shiftr huff drop + Z.of_nat r * incr)) with true by (symmetry; apply Z.leb_le; lia).
      replace (next + (Z.shiftr huff drop + Z.of_nat r * incr) <? next + Z.shiftr huff drop + Z.of_nat r * incr) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (next + (Z.shiftr huff drop + Z.of_nat r * incr) <? next + Z.shiftr huff drop + Z.of_nat (S r) * incr) with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [andb]. destruct ((0 <=? _) && _); reflexivity.
    + destruct (Z.leb_spec (next + Z.shiftr huff drop) x); cbn [andb]; [|reflexivity].
      destruct (Z.ltb_spec x (next + Z.shiftr huff drop + Z.of_nat r * incr)); cbn [andb].
      * replace (x <? next + Z.shiftr huff drop + Z.of_nat (S r) * incr) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. reflexivity.
      * destruct (Z.ltb_spec x (next + Z.shiftr huff drop + Z.of_nat (S r) * incr)); cbn [andb]; [|reflexivity].
        destruct (Z.eqb_spec ((x - (next + Z.shiftr huff drop)) mod incr) 0); cbn [andb]; [|reflexivity].
        exfalso. apply E. pose proof (Z.div_mod (x - (next + Z.shiftr huff drop)) incr ltac:(lia)) as DM.
        assert ((x - (next + Z.shiftr huff drop)) / incr = Z.of_nat r); [|nia].
        symmetry. apply Z.div_unique with (r := x - (next + Z.shiftr huff drop) - Z.of_nat r * incr); [left|]; nia.
Qed.

Lemma it_fill_spec : forall here i f huff drop next tbl,
  0 <= i <= f -> f <= 31 ->
  let h := Z.shiftr huff drop in
  let res := it_fill here (2 ^ i) huff drop next (2 ^ f) tbl in
  arr_len res = arr_len tbl /\
  forall x, arr_get res x =
    if fill_hits (next + h) (2 ^ i) (2 ^ (f - i)) x && arr_inb tbl x then here else arr_get tbl x.
Proof.
  intros here i f huff drop next tbl Hif Hf. cbv zeta. rewrite it_fill_eq.
  pose proof (pow2_pos i ltac:(lia)) as Pi. pose proof (pow2_pos (f - i) ltac:(lia)) as Pfi.
  assert (E : 2 ^ f = Z.of_nat (Z.to_nat (2 ^ (f - i))) * 2 ^ i).
  { rewrite Z2Nat.id by lia. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (B32 : 2 ^ f < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
  rewrite E.
  destruct (it_fill_loop here (2 ^ i) huff drop next tbl (Z.to_nat (2 ^ (f - i))) (Z.of_nat (Z.to_nat (2 ^ (f - i))) * 2 ^ i) tbl
              Pi ltac:(lia) ltac:(rewrite <- E; exact B32) ltac:(nia) eq_refl) as [A Bx].
  split; [exact A|]. intros x. rewrite Bx. rewrite Z2Nat.id by lia. reflexivity.
Qed.


Section Concrete.
  Variables (lens : arr) (lens_ofs codes : Z).
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall s, 0 <= s < codes -> 0 <= arr_get lens (lens_ofs + s) <= 15.

  Let Nn := N lens lens_ofs codes.
  Let Wl := W lens lens_ofs codes.
  Let mx := max lens lens_ofs codes.
  Let mn := min lens lens_ofs codes.
  Let cntf := cnt lens lens_ofs codes.
  Let cof := coff lens lens_ofs codes.

  Definition Lf (i : Z) : Z := L lens lens_ofs (znth 0 Wl i).

  Lemma Lf_range : forall i, 0 <= i < Nn -> 1 <= Lf i <= 15.
  Proof. intros i Hi. unfold Lf. apply (W_spec lens lens_ofs codes Hcodes i Hi). Qed.
  Lemma Lf_sorted : forall i j, 0 <= i <= j -> j < Nn -> Lf i <= Lf j.
  Proof. intros i j Hij Hj. unfold Lf. apply (W_sorted lens lens_ofs codes Hcodes); lia. Qed.
  Lemma W_range : forall i, 0 <= i < Nn -> 0 <= znth 0 Wl i < codes.
  Proof. intros i Hi. apply (W_spec lens lens_ofs codes Hcodes i Hi). Qed.
  Lemma Lf_block : forall l i, 1 <= l <= 15 -> cof l <= i < cof l + cntf l -> Lf i = l.
  Proof. intros l i Hl Hi. unfold Lf. apply (W_block_spec lens lens_ofs codes Hcodes l i Hl Hi). Qed.

  Lemma sum_by_blocks : forall g : Z -> Z,
    sumZ (fun i => g (Lf i)) 0 Nn = sumZ (fun l => cntf l * g l) 1 16.
  Proof.
    intros g.
    assert (G : forall n, (n <= 15)%nat ->
      sumZ (fun i => g (Lf i)) 0 (cof (Z.of_nat n + 1)) = sumZ (fun l => cntf l * g l) 1 (Z.of_nat n + 1)).
    { induction n as [|n IH]; intros Hn.
      - change (Z.of_nat 0 + 1) with 1. unfold cof. rewrite coff_1. rewrite !sumZ_nil by lia. reflexivity.
      - replace (Z.of_nat (S n) + 1) with (Z.of_nat n + 1 + 1) by lia.
        unfold cof in *. rewrite coff_step by lia.
        pose proof (coff_range lens lens_ofs codes Hcodes (Z.of_nat n + 1) ltac:(lia)) as CR.
        pose proof (cnt_range lens lens_ofs codes Hcodes (Z.of_nat n + 1)) as NR.
        rewrite (sumZ_split _ 0 (coff lens lens_ofs codes (Z.of_nat n + 1)) (coff lens lens_ofs codes (Z.of_nat n + 1) + cnt lens lens_ofs codes (Z.of_nat n + 1))) by lia.
        rewrite IH by lia. rewrite (sumZ_snoc _ 1 (Z.of_nat n + 1)) by lia.
        rewrite (sumZ_ext (fun i : Z => g (Lf i)) (fun _ => g (Z.of_nat n + 1)) (coff lens lens_ofs codes (Z.of_nat n + 1))).
        2: { intros j Hj. f_equal. apply Lf_block; [lia|]. unfold cof, cntf. lia. }
        assert (CST : forall c lo hi, lo <= hi -> sumZ (fun _ => c) lo hi = (hi - lo) * c).
        { intros c lo hi Hlh. unfold sumZ. remember (Z.to_nat (hi - lo)) as k eqn:Hk. assert (hi - lo = Z.of_nat k) as -> by lia.
          clear. induction k; cbn [sumN]; lia. }
        rewrite CST by lia. unfold cntf. lia. }
    pose proof (G 15%nat ltac:(lia)) as E. change (Z.of_nat 15 + 1) with 16 in E.
    unfold cof in E. rewrite coff_16 in E. exact E.
  Qed.

  Lemma remf_cnt : forall l, 1 <= l <= 15 -> remf Nn Lf 0 l = cntf l.
  Proof.
    intros l Hl. unfold remf.
    rewrite (sum_by_blocks (fun v => if v =? l then 1 else 0)).
    rewrite (sumZ_one _ 1 l 16) by (try lia; intros i Hi Hne; replace (i =? l) with false by (symmetry; apply Z.eqb_neq; lia); lia).
    rewrite Z.eqb_refl. lia.
  Qed.

  Lemma SK_kraft : SK Lf Nn = kraft lens lens_ofs codes 15.
  Proof.
    unfold SK, T, kraft. change (15 + 1) with 16.
    apply (sum_by_blocks (fun v => 2 ^ (15 - v))).
  Qed.

  Hypothesis Hmax : 1 <= mx.

  Lemma N_pos : 1 <= Nn.
  Proof.
    destruct (max_spec lens lens_ofs codes Hcodes Hlens) as (A & B & C).
    destruct B as [B|B]; [unfold mx in Hmax; lia|].
    pose proof (coff_range lens lens_ofs codes Hcodes (mx + 1) ltac:(unfold mx in *; lia)) as CR.
    rewrite coff_step in CR by (unfold mx in *; lia).
    pose proof (coff_range lens lens_ofs codes Hcodes mx ltac:(unfold mx in *; lia)).
    pose proof (cnt_range lens lens_ofs codes Hcodes mx). unfold mx, Nn in *. lia.
  Qed.

  Lemma Lf_first : Lf 0 = mn.
  Proof.
    destruct (max_spec lens lens_ofs codes Hcodes Hlens) as (A & B & C).
    destruct (min_spec lens lens_ofs codes Hcodes Hlens ltac:(unfold mx in Hmax; exact Hmax)) as (A' & B' & C').
    pose proof N_pos as NP.
    destruct (W_index_block lens lens_ofs codes 0 ltac:(unfold Nn in NP; lia)) as (l & Hl & Hb).
    rewrite (Lf_block l 0 Hl Hb).
    pose proof (cnt_range lens lens_ofs codes Hcodes l).
    pose proof (coff_range lens lens_ofs codes Hcodes l ltac:(lia)).
    assert (Hc0 : coff lens lens_ofs codes l = 0) by lia.
    destruct (Z_lt_le_dec l (min lens lens_ofs codes)). { exfalso. pose proof (C' l ltac:(lia)). lia. }
    destruct (Z_lt_le_dec (min lens lens_ofs codes) l); [|unfold mn; lia]. exfalso.
    assert (Z0 : cnt lens lens_ofs codes (min lens lens_ofs codes) = 0).
    { pose proof (coff_mono lens lens_ofs codes Hcodes (min lens lens_ofs codes + 1) l ltac:(lia)) as M.
      rewrite coff_step in M by lia. pose proof (coff_range lens lens_ofs codes Hcodes (min lens lens_ofs codes) ltac:(lia)).
      pose proof (cnt_range lens lens_ofs codes Hcodes (min lens lens_ofs codes)). lia. }
    destruct B' as [B'|B']; [|lia]. destruct B as [B|B]; [unfold mx in Hmax; lia|]. rewrite B' in Z0. unfold mx in *. lia.
  Qed.

  Lemma Lf_last : Lf (Nn - 1) = mx.
  Proof.
    destruct (max_spec lens lens_ofs codes Hcodes Hlens) as (A & B & C).
    pose proof N_pos as NP.
    destruct (W_index_block lens lens_ofs codes (Nn - 1) ltac:(unfold Nn in *; lia)) as (l & Hl & Hb).
    rewrite (Lf_block l (Nn - 1) Hl Hb).
    pose proof (cnt_range lens lens_ofs codes Hcodes l).
    pose proof (coff_range lens lens_ofs codes Hcodes (l + 1) ltac:(lia)) as CR1. rewrite coff_step in CR1 by lia.
    destruct (Z_lt_le_dec (max lens lens_ofs codes) l). { exfalso. pose proof (C l ltac:(lia)). lia. }
    destruct (Z_lt_le_dec l (max lens lens_ofs codes)); [|unfold mx; lia]. exfalso.
    destruct B as [B|B]; [unfold mx in Hmax; lia|]. apply B.
    pose proof (coff_mono lens lens_ofs codes Hcodes (l + 1) (max lens lens_ofs codes) ltac:(lia)) as M.
    rewrite coff_step in M by lia.
    pose proof (coff_range lens lens_ofs codes Hcodes (max lens lens_ofs codes + 1) ltac:(lia)) as CR2. rewrite coff_step in CR2 by lia.
    pose proof (cnt_range lens lens_ofs codes Hcodes (max lens lens_ofs codes)). unfold Nn in *. lia.
  Qed.
End Concrete.
