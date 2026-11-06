(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxFold FxFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma find_rg_spec : forall fs rgs a w i0 i R o, find_rg fs rgs a w i0 = Some (i, R, o) ->
  (i0 <= i)%nat /\ nth_error rgs (i - i0) = Some R /\ rg_off fs R a w = Some o.
Proof.
  intros fs. induction rgs as [|R0 rs IH]; intros a w i0 i R o H; cbn [find_rg] in H; [discriminate|].
  destruct (rg_off fs R0 a w) as [o0|] eqn:Ho.
  - injection H as <- <- <-. split; [lia|]. rewrite Nat.sub_diag. split; [reflexivity | exact Ho].
  - destruct (IH a w (S i0) i R o H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
    replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn.
Qed.

Lemma nth_upd_same : forall rgs i R R0, nth_error rgs i = Some R0 -> nth_error (upd_nth rgs i R) i = Some R.
Proof. induction rgs as [|x rs IH]; intros [|i] R R0 H; cbn in *; try discriminate; [reflexivity | eapply IH; exact H]. Qed.
Lemma nth_upd_other : forall rgs i j R, i <> j -> nth_error (upd_nth rgs i R) j = nth_error rgs j.
Proof. induction rgs as [|x rs IH]; intros [|i] [|j] R Hne; cbn; try reflexivity; [lia | apply IH; lia]. Qed.
Lemma length_upd : forall rgs i R, length (upd_nth rgs i R) = length rgs.
Proof. induction rgs as [|x rs IH]; intros [|i] R; cbn; try reflexivity; rewrite IH; reflexivity. Qed.

Lemma Forall_nth' : forall {A} (P : A -> Prop) l, Forall P l <-> (forall i x, nth_error l i = Some x -> P x).
Proof.
  intros A P l. split.
  - intros H i x Hx. rewrite Forall_forall in H. apply H. eapply nth_error_In. exact Hx.
  - intros H. apply Forall_forall. intros x Hx. apply In_nth_error in Hx as [i Hi]. exact (H i x Hi).
Qed.

Lemma rgs_disj_nth : forall E rgs i j R1 R2, rgs_disj E rgs -> i <> j ->
  nth_error rgs i = Some R1 -> nth_error rgs j = Some R2 -> rg_disj E R1 R2.
Proof.
  induction rgs as [|x rs IH]; intros i j R1 R2 Hd Hij H1 H2; [destruct i; discriminate|].
  destruct Hd as [Hx Hrs]. destruct i as [|i]; destruct j as [|j]; cbn in H1, H2; try lia.
  - injection H1 as <-. rewrite Forall_forall in Hx. apply Hx. eapply nth_error_In. exact H2.
  - injection H2 as <-. rewrite Forall_forall in Hx. pose proof (Hx R1 ltac:(eapply nth_error_In; exact H1)) as Hd.
    unfold rg_disj in *. lia.
  - eapply IH; [exact Hrs | | exact H1 | exact H2]. lia.
Qed.

Lemma rg_disj_same_shape : forall E R1 R1' R2, rg_base R1' = rg_base R1 -> rg_size R1' = rg_size R1 ->
  (rg_disj E R1 R2 <-> rg_disj E R1' R2) /\ (rg_disj E R2 R1 <-> rg_disj E R2 R1').
Proof. intros E R1 R1' R2 Hb Hs. unfold rg_disj, rsz. rewrite Hb, Hs. tauto. Qed.

Lemma rgs_disj_upd : forall E rgs i R R0, nth_error rgs i = Some R0 -> rg_base R = rg_base R0 -> rg_size R = rg_size R0 ->
  rgs_disj E rgs -> rgs_disj E (upd_nth rgs i R).
Proof.
  induction rgs as [|x rs IH]; intros [|i] R R0 Hn Hb Hs Hd; cbn in *; try discriminate.
  - injection Hn as <-. destruct Hd as [Hx Hrs]. split; [|exact Hrs].
    eapply Forall_impl; [|exact Hx]. intros y Hy. apply (rg_disj_same_shape E x R y Hb Hs). exact Hy.
  - destruct Hd as [Hx Hrs]. split; [|eapply IH; eassumption].
    apply Forall_nth'. intros j y Hy. destruct (Nat.eq_dec i j) as [->|Hne].
    + rewrite (nth_upd_same rs j R R0 Hn) in Hy. injection Hy as <-.
      rewrite Forall_nth' in Hx. apply (rg_disj_same_shape E R0 R x Hb Hs). exact (Hx j R0 Hn).
    + rewrite nth_upd_other in Hy by exact Hne. rewrite Forall_nth' in Hx. exact (Hx j y Hy).
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_frame : forall E m m' R,
  rg_ok segs E m R ->
  (forall x : word, bv_unsigned (lden E (rg_base R)) <= bv_unsigned x < bv_unsigned (lden E (rg_base R)) + rsz E R -> m' x = m x) ->
  rg_ok segs E m' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m m' R (Hsz & Hflat & Hall & Hcont) Hfr.
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R))) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with two64 in RA.
  split; [exact Hsz|]. split; [exact Hflat|]. split.
  - intros i Hi. specialize (Hall i Hi).
    assert (He : m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i))).
    { apply Hfr. rewrite u_small64 by lia. lia. }
    destruct (rg_kind R); unfold rd1, wview in *; rewrite He; exact Hall.
  - intros p v Hp. destruct (Hcont p v Hp) as [Hp1 Hp2]. split; [exact Hp1|].
    pose proof (Pos2Z.is_pos p).
    unfold rd1 in *. rewrite Hfr; [exact Hp2|]. rewrite u_small64 by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rgs_frame_write : forall E m rgs i R0 o bs,
  Forall (rg_ok segs E m) rgs -> rgs_disj E rgs -> nth_error rgs i = Some R0 ->
  0 <= o -> o + Z.of_nat (length bs) <= rsz E R0 ->
  forall j R, j <> i -> nth_error rgs j = Some R ->
    rg_ok segs E (write_to_mem m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R0)) + o)) bs) R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m rgs i R0 o bs Hok Hd Hi Ho Hn j R Hji Hj.
  rewrite Forall_nth' in Hok. pose proof (Hok i R0 Hi) as HR0. pose proof (Hok j R Hj) as HR.
  pose proof (rgs_disj_nth E rgs j i R R0 Hd Hji Hj Hi) as Hdis.
  destruct HR0 as (_ & Hflat0 & _ & _).
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R0))) as RA0. unfold bv_modulus in RA0. change (2 ^ Z.of_N 64) with two64 in RA0.
  apply rg_ok_frame with (m := m); [exact HR|].
  intros x Hx. rewrite write_to_mem_spec by lia.
  destruct (Z.leb (bv_unsigned (lden E (rg_base R0)) + o) (bv_unsigned x) &&
            Z.ltb (bv_unsigned x) (bv_unsigned (lden E (rg_base R0)) + o + Z.of_nat (length bs)))%bool eqn:E1; [|reflexivity].
  apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  unfold rg_disj in Hdis. lia.
Qed.

End WithSegs.

(* [comment removed for export] *)
Lemma tfilter_acc_spec : forall {A} (f : positive -> bool) (t : tree A) k p,
  tget p (tfilter_acc f t k) = match tget p t with Some x => if f (k p) then Some x else None | None => None end.
Proof.
  intros A f t. induction t as [|l IHl v r IHr]; intros k p; [cbn [tfilter_acc]; rewrite !tget_empty; reflexivity|].
  destruct p as [p|p|]; cbn [tfilter_acc tget]; [exact (IHr (fun q => k (xI q)) p) | exact (IHl (fun q => k (xO q)) p) | destruct v; reflexivity].
Qed.
Lemma tget_tfilter : forall {A} (f : positive -> bool) (t : tree A) p,
  tget p (tfilter f t) = match tget p t with Some x => if f p then Some x else None | None => None end.
Proof. intros. apply tfilter_acc_spec. Qed.

(* [comment removed for export] *)
Lemma size_lo_sound : forall E fs R, Forall (fact_ok E) fs -> size_lo fs R <= rsz E R.
Proof.
  intros E fs R HF. unfold size_lo, rsz. destruct (is_const (rg_size R)) as [c|] eqn:Hc.
  - destruct (is_const_sound E _ c Hc) as [-> Hr]. rewrite u_small64 by lia. lia.
  - exact (proj1 (irange_sound E fs (rg_size R) HF)).
Qed.

Lemma rsz_lconst : forall E b n k c, 0 <= n < two64 -> rsz E (RG b (lconst n) k c) = n.
Proof. intros E b n k c Hn. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by lia. reflexivity. Qed.
Lemma rsz_const : forall E R n, rg_size R = lconst n -> 0 <= n < two64 -> rsz E R = n.
Proof. intros E R n Hs Hn. unfold rsz. rewrite Hs, lden_lconst, u_small64 by lia. reflexivity. Qed.
Lemma rsz_RGz : forall E b n k c, 0 <= n < two64 -> rsz E (RGz b n k c) = n.
Proof. intros E b n k c Hn. exact (rsz_lconst E b n k c Hn). Qed.

Lemma rg_off_sym_sound : forall E fs R a w lo hi, Forall (fact_ok E) fs -> rg_off_sym fs R a w = Some (lo, hi) ->
  exists o, lo <= o <= hi /\ 0 <= o /\ o + w <= rsz E R /\ lden E a = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o).
Proof.
  intros E fs R a w lo hi HF H. unfold rg_off_sym in H. pose proof (size_lo_sound E fs R HF) as Hsz.
  pose proof (irange_sound E fs (lsub a (rg_base R)) HF) as Hlo.
  destruct (irange fs (lsub a (rg_base R))) as [lo0 hi0] eqn:Hr. cbn [fst snd] in Hlo.
  destruct (Z.leb 0 lo0) eqn:H1; [|discriminate]. apply Z.leb_le in H1.
  assert (Hin : bv_unsigned (lden E (lsub a (rg_base R))) + w <= rsz E R /\ lo0 = lo /\ hi0 = hi).
  { revert H. destruct (Z.leb (hi0 + w) (size_lo fs R)) eqn:H2; intros H.
    - injection H as <- <-. apply Z.leb_le in H2. split; [lia | split; reflexivity].
    - revert H. destruct (rel_in fs R a w hi0) eqn:H3; intros H; [|discriminate]. injection H as <- <-. split; [|split; reflexivity].
      unfold rel_in in H3.
      pose proof (irange_sound E fs (lsub (rg_size R) (lsub a (rg_base R))) HF) as Hd.
      pose proof (irange_sound E fs (rg_size R) HF) as Hs.
      destruct (irange fs (lsub (rg_size R) (lsub a (rg_base R)))) as [dlo dhi]. cbn [fst snd] in Hd.
      destruct (irange fs (rg_size R)) as [slo shi]. cbn [fst snd] in Hs, H3.
      apply andb_prop in H3 as [H3 H6]. apply andb_prop in H3 as [H3 H5]. apply andb_prop in H3 as [H3 H4].
      apply Z.leb_le in H3. apply Z.ltb_lt in H4, H5, H6.
      rewrite lden_lsub, bv_sub_unsigned in Hd. unfold bv_wrap, bv_modulus in Hd. unfold rsz.
      set (S0 := bv_unsigned (lden E (rg_size R))) in *. set (O0 := bv_unsigned (lden E (lsub a (rg_base R)))) in *.
      change (2 ^ Z.of_N 64) with 18446744073709551616 in Hd.
      assert (HS0 : 0 <= S0) by (unfold S0; pose proof (bv_unsigned_in_range _ (lden E (rg_size R))); lia).
      destruct (Z_lt_le_dec (S0 - O0) 0) as [Hneg|Hpos].
      + rewrite <- (Z.mod_unique (S0 - O0) 18446744073709551616 (-1) (S0 - O0 + 18446744073709551616)) in Hd by lia. lia.
      + rewrite Z.mod_small in Hd by lia. lia. }
  destruct Hin as (Hin & <- & <-).
  exists (bv_unsigned (lden E (lsub a (rg_base R)))). split; [exact Hlo|]. split; [lia|]. split; [exact Hin|].
  rewrite lden_lsub. apply bv_eq. rewrite Z_to_bv_unsigned, bv_sub_unsigned. unfold bv_wrap.
  rewrite Z.add_mod_idemp_r by (unfold bv_modulus; lia).
  replace (bv_unsigned (lden E (rg_base R)) + (bv_unsigned (lden E a) - bv_unsigned (lden E (rg_base R)))) with (bv_unsigned (lden E a)) by lia.
  symmetry. apply Z.mod_small. apply bv_unsigned_in_range.
Qed.

Lemma rg_off_symx_sound : forall E fs R a w lo hi, Forall (fact_ok E) fs -> rg_off_symx fs R a w = Some (lo, hi) ->
  exists o, lo <= o <= hi /\ 0 <= o /\ o + w <= rsz E R /\ lden E a = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o).
Proof.
  intros E fs R a w lo hi HF H. unfold rg_off_symx in H. pose proof (size_lo_sound E fs R HF) as Hsz.
  pose proof (irange_x_sound E fs (lsub a (rg_base R)) HF) as Hlo.
  destruct (irange_x fs (lsub a (rg_base R))) as [lo0 hi0] eqn:Hr. cbn [fst snd] in Hlo.
  destruct (Z.leb 0 lo0) eqn:H1; [|discriminate]. apply Z.leb_le in H1.
  assert (Hin : bv_unsigned (lden E (lsub a (rg_base R))) + w <= rsz E R /\ lo0 = lo /\ hi0 = hi).
  { revert H. destruct (Z.leb (hi0 + w) (size_lo fs R)) eqn:H2; intros H.
    - injection H as <- <-. apply Z.leb_le in H2. split; [lia | split; reflexivity].
    - revert H. destruct (rel_inx fs R a w hi0) eqn:H3; intros H; [|discriminate]. injection H as <- <-. split; [|split; reflexivity].
      unfold rel_inx in H3.
      pose proof (irange_x_sound E fs (lsub (rg_size R) (lsub a (rg_base R))) HF) as Hd.
      pose proof (irange_x_sound E fs (rg_size R) HF) as Hs.
      destruct (irange_x fs (lsub (rg_size R) (lsub a (rg_base R)))) as [dlo dhi]. cbn [fst snd] in Hd.
      destruct (irange_x fs (rg_size R)) as [slo shi]. cbn [fst snd] in Hs, H3.
      apply andb_prop in H3 as [H3 H6]. apply andb_prop in H3 as [H3 H5]. apply andb_prop in H3 as [H3 H4].
      apply Z.leb_le in H3. apply Z.ltb_lt in H4, H5, H6.
      rewrite lden_lsub, bv_sub_unsigned in Hd. unfold bv_wrap, bv_modulus in Hd. unfold rsz.
      set (S0 := bv_unsigned (lden E (rg_size R))) in *. set (O0 := bv_unsigned (lden E (lsub a (rg_base R)))) in *.
      change (2 ^ Z.of_N 64) with 18446744073709551616 in Hd.
      assert (HS0 : 0 <= S0) by (unfold S0; pose proof (bv_unsigned_in_range _ (lden E (rg_size R))); lia).
      destruct (Z_lt_le_dec (S0 - O0) 0) as [Hneg|Hpos].
      + rewrite <- (Z.mod_unique (S0 - O0) 18446744073709551616 (-1) (S0 - O0 + 18446744073709551616)) in Hd by lia. lia.
      + rewrite Z.mod_small in Hd by lia. lia. }
  destruct Hin as (Hin & <- & <-).
  exists (bv_unsigned (lden E (lsub a (rg_base R)))). split; [exact Hlo|]. split; [lia|]. split; [exact Hin|].
  rewrite lden_lsub. apply bv_eq. rewrite Z_to_bv_unsigned, bv_sub_unsigned. unfold bv_wrap.
  rewrite Z.add_mod_idemp_r by (unfold bv_modulus; lia).
  replace (bv_unsigned (lden E (rg_base R)) + (bv_unsigned (lden E a) - bv_unsigned (lden E (rg_base R)))) with (bv_unsigned (lden E a)) by lia.
  symmetry. apply Z.mod_small. apply bv_unsigned_in_range.
Qed.
(* [comment removed for export] *)
Definition rg_off_cz (fs : list fact) (R : region) (a : lin) (w lo hi : Z) : Prop :=
  exists win c z, (win = irange fs a \/ win = irange_x fs a) /\ rg_cz R = Some (c, z) /\
    c <= fst win /\ snd win + w <= c + z /\ lo = fst win - c /\ hi = snd win - c.
Lemma rg_off_cz_sound : forall E fs R a w lo hi, Forall (fact_ok E) fs -> rg_off_cz fs R a w lo hi ->
  exists o, lo <= o <= hi /\ 0 <= o /\ o + w <= rsz E R /\ lden E a = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o).
Proof.
  intros E fs R a w lo hi HF (win & c & z & Hwin & Hcz & H1 & H2 & -> & ->).
  assert (Hw : fst win <= bv_unsigned (lden E a) <= snd win)
    by (destruct Hwin as [->| ->]; [exact (irange_sound E fs a HF) | exact (irange_x_sound E fs a HF)]).
  unfold rg_cz in Hcz. destruct (is_const (rg_base R)) as [c0|] eqn:Hb; [|discriminate]. destruct (is_const (rg_size R)) as [z0|] eqn:Hs; [|discriminate].
  injection Hcz as -> ->. rewrite (is_const_u E _ c Hb). unfold rsz. rewrite (is_const_u E _ z Hs).
  exists (bv_unsigned (lden E a) - c). split; [lia|]. split; [lia|]. split; [lia|].
  apply bv_eq. rewrite Z_to_bv_unsigned. replace (c + (bv_unsigned (lden E a) - c)) with (bv_unsigned (lden E a)) by lia.
  unfold bv_wrap. symmetry. apply Z.mod_small. apply bv_unsigned_in_range.
Qed.
(* [comment removed for export] *)
Definition rg_off_any (fs : list fact) (R : region) (a : lin) (w lo hi : Z) : Prop :=
  rg_off_sym fs R a w = Some (lo, hi) \/ rg_off_symx fs R a w = Some (lo, hi) \/ rg_off_cz fs R a w lo hi.
Lemma rg_off_any_sound : forall E fs R a w lo hi, Forall (fact_ok E) fs -> rg_off_any fs R a w lo hi ->
  exists o, lo <= o <= hi /\ 0 <= o /\ o + w <= rsz E R /\ lden E a = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o).
Proof.
  intros E fs R a w lo hi HF [H|[H|H]]; [exact (rg_off_sym_sound E fs R a w lo hi HF H) | exact (rg_off_symx_sound E fs R a w lo hi HF H) | exact (rg_off_cz_sound E fs R a w lo hi HF H)].
Qed.
Lemma rg_off_any_lo : forall fs R a w lo hi, rg_off_any fs R a w lo hi -> 0 <= lo.
Proof.
  intros fs R a w lo hi [Ho|[Ho|(win & c & z & _ & _ & H1 & _ & -> & _)]]; [| |lia].
  - unfold rg_off_sym in Ho. destruct (irange fs (lsub a (rg_base R))) as [lo1 hi1]. destruct (Z.leb 0 lo1) eqn:Hl1; [|discriminate].
    apply Z.leb_le in Hl1. destruct (Z.leb (hi1 + w) (size_lo fs R)); [injection Ho as <- <-; exact Hl1|].
    destruct (rel_in fs R a w hi1); [injection Ho as <- <-; exact Hl1 | discriminate].
  - unfold rg_off_symx in Ho. destruct (irange_x fs (lsub a (rg_base R))) as [lo1 hi1]. destruct (Z.leb 0 lo1) eqn:Hl1; [|discriminate].
    apply Z.leb_le in Hl1. destruct (Z.leb (hi1 + w) (size_lo fs R)); [injection Ho as <- <-; exact Hl1|].
    destruct (rel_inx fs R a w hi1); [injection Ho as <- <-; exact Hl1 | discriminate].
Qed.

Lemma find_rg_c_spec : forall win w rgs i0 i R lo hi, find_rg_c win w rgs i0 = Some (i, R, (lo, hi)) ->
  (i0 <= i)%nat /\ nth_error rgs (i - i0) = Some R /\
  exists c z, rg_cz R = Some (c, z) /\ c <= fst win /\ snd win + w <= c + z /\ lo = fst win - c /\ hi = snd win - c.
Proof.
  intros win w rgs. induction rgs as [|R0 rs IH]; intros i0 i R lo hi H; cbn [find_rg_c] in H; [discriminate|].
  destruct (rg_cz R0) as [[c z]|] eqn:Hcz.
  - destruct (Z.leb c (fst win) && Z.leb (snd win + w) (c + z))%bool eqn:Hb.
    + injection H as <- <- <- <-. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
      split; [lia|]. rewrite Nat.sub_diag. split; [reflexivity|]. exists c, z. repeat split; assumption.
    + destruct (IH (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
      replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn.
  - destruct (IH (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
    replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn.
Qed.
Lemma find_rg_sym1_spec : forall fs rgs a w i0 i R lo hi, find_rg_sym1 fs rgs a w i0 = Some (i, R, (lo, hi)) ->
  (i0 <= i)%nat /\ nth_error rgs (i - i0) = Some R /\ rg_off_sym fs R a w = Some (lo, hi).
Proof.
  intros fs rgs. induction rgs as [|R0 rs IH]; intros a w i0 i R lo hi H; cbn [find_rg_sym1] in H; [discriminate|].
  destruct (rg_cz R0) as [cz|] eqn:Hcz.
  { destruct (IH a w (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
    replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn. }
  destruct (rg_off_sym fs R0 a w) as [[lo0 hi0]|] eqn:Ho.
  - injection H as <- <- <- <-. split; [lia|]. rewrite Nat.sub_diag. split; [reflexivity | exact Ho].
  - destruct (IH a w (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
    replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn.
Qed.
Lemma find_rg_symx_spec : forall fs rgs a w i0 i R lo hi, find_rg_symx fs rgs a w i0 = Some (i, R, (lo, hi)) ->
  (i0 <= i)%nat /\ nth_error rgs (i - i0) = Some R /\ rg_off_symx fs R a w = Some (lo, hi).
Proof.
  intros fs rgs. induction rgs as [|R0 rs IH]; intros a w i0 i R lo hi H; cbn [find_rg_symx] in H; [discriminate|].
  destruct (rg_cz R0) as [cz|] eqn:Hcz.
  { destruct (IH a w (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
    replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn. }
  destruct (rg_off_symx fs R0 a w) as [[lo0 hi0]|] eqn:Ho.
  - injection H as <- <- <- <-. split; [lia|]. rewrite Nat.sub_diag. split; [reflexivity | exact Ho].
  - destruct (IH a w (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
    replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn.
Qed.
Lemma find_rg_sym1a_spec : forall fs rgs a w i0 i R lo hi, find_rg_sym1a fs rgs a w i0 = Some (i, R, (lo, hi)) ->
  (i0 <= i)%nat /\ nth_error rgs (i - i0) = Some R /\ rg_off_sym fs R a w = Some (lo, hi).
Proof.
  intros fs rgs. induction rgs as [|R0 rs IH]; intros a w i0 i R lo hi H; cbn [find_rg_sym1a] in H; [discriminate|].
  destruct (rg_off_sym fs R0 a w) as [[lo0 hi0]|] eqn:Ho.
  - injection H as <- <- <- <-. split; [lia|]. rewrite Nat.sub_diag. split; [reflexivity | exact Ho].
  - destruct (IH a w (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
    replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn.
Qed.
Lemma find_rg_symxa_spec : forall fs rgs a w i0 i R lo hi, find_rg_symxa fs rgs a w i0 = Some (i, R, (lo, hi)) ->
  (i0 <= i)%nat /\ nth_error rgs (i - i0) = Some R /\ rg_off_symx fs R a w = Some (lo, hi).
Proof.
  intros fs rgs. induction rgs as [|R0 rs IH]; intros a w i0 i R lo hi H; cbn [find_rg_symxa] in H; [discriminate|].
  destruct (rg_off_symx fs R0 a w) as [[lo0 hi0]|] eqn:Ho.
  - injection H as <- <- <- <-. split; [lia|]. rewrite Nat.sub_diag. split; [reflexivity | exact Ho].
  - destruct (IH a w (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
    replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn.
Qed.
Lemma find_rg_symP_spec : forall p fs rgs a w i0 i R lo hi, find_rg_symP p fs rgs a w i0 = Some (i, R, (lo, hi)) ->
  (i0 <= i)%nat /\ nth_error rgs (i - i0) = Some R /\ rg_off_sym fs R a w = Some (lo, hi).
Proof.
  intros p fs rgs. induction rgs as [|R0 rs IH]; intros a w i0 i R lo hi H; cbn [find_rg_symP] in H; [discriminate|].
  destruct (p R0).
  - destruct (rg_off_sym fs R0 a w) as [[lo0 hi0]|] eqn:Ho.
    + injection H as <- <- <- <-. split; [lia|]. rewrite Nat.sub_diag. split; [reflexivity | exact Ho].
    + destruct (IH a w (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
      replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn.
  - destruct (IH a w (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
    replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn.
Qed.
Lemma find_rg_symxP_spec : forall p fs rgs a w i0 i R lo hi, find_rg_symxP p fs rgs a w i0 = Some (i, R, (lo, hi)) ->
  (i0 <= i)%nat /\ nth_error rgs (i - i0) = Some R /\ rg_off_symx fs R a w = Some (lo, hi).
Proof.
  intros p fs rgs. induction rgs as [|R0 rs IH]; intros a w i0 i R lo hi H; cbn [find_rg_symxP] in H; [discriminate|].
  destruct (p R0).
  - destruct (rg_off_symx fs R0 a w) as [[lo0 hi0]|] eqn:Ho.
    + injection H as <- <- <- <-. split; [lia|]. rewrite Nat.sub_diag. split; [reflexivity | exact Ho].
    + destruct (IH a w (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
      replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn.
  - destruct (IH a w (S i0) i R lo hi H) as (Hi & Hn & Hr). split; [lia|]. split; [|exact Hr].
    replace (i - i0)%nat with (S (i - S i0)) by lia. exact Hn.
Qed.
(* [comment removed for export] *)
Lemma find_rg_sym_spec : forall fs rgs a w i0 i R lo hi, find_rg_sym fs rgs a w i0 = Some (i, R, (lo, hi)) ->
  (i0 <= i)%nat /\ nth_error rgs (i - i0) = Some R /\ rg_off_any fs R a w lo hi.
Proof.
  intros fs rgs a w i0 i R lo hi H. unfold find_rg_sym in H.
  destruct (find_rg_c (irange fs a) w rgs i0) as [r|] eqn:H0.
  { injection H as ->. destruct (find_rg_c_spec _ _ _ _ _ _ _ _ H0) as (A & B & c & z & C1 & C2 & C3 & C4 & C5).
    split; [exact A | split; [exact B | right; right; exists (irange fs a), c, z; split; [left; reflexivity | tauto]]]. }
  destruct (find_rg_symP (rg_pick a true) fs rgs a w i0) as [r|] eqn:H1.
  { injection H as ->. destruct (find_rg_symP_spec _ _ _ _ _ _ _ _ _ _ H1) as (A & B & C). split; [exact A | split; [exact B | left; exact C]]. }
  destruct (find_rg_symP (rg_pick a false) fs rgs a w i0) as [r|] eqn:H1'.
  { injection H as ->. destruct (find_rg_symP_spec _ _ _ _ _ _ _ _ _ _ H1') as (A & B & C). split; [exact A | split; [exact B | left; exact C]]. }
  destruct (find_rg_c (irange_x fs a) w rgs i0) as [r|] eqn:H2.
  { injection H as ->. destruct (find_rg_c_spec _ _ _ _ _ _ _ _ H2) as (A & B & c & z & C1 & C2 & C3 & C4 & C5).
    split; [exact A | split; [exact B | right; right; exists (irange_x fs a), c, z; split; [right; reflexivity | tauto]]]. }
  destruct (find_rg_symxP (rg_pick a true) fs rgs a w i0) as [r|] eqn:H3.
  { injection H as ->. destruct (find_rg_symxP_spec _ _ _ _ _ _ _ _ _ _ H3) as (A & B & C). split; [exact A | split; [exact B | right; left; exact C]]. }
  destruct (find_rg_symxP (rg_pick a false) fs rgs a w i0) as [r|] eqn:H3'.
  { injection H as ->. destruct (find_rg_symxP_spec _ _ _ _ _ _ _ _ _ _ H3') as (A & B & C). split; [exact A | split; [exact B | right; left; exact C]]. }
  destruct (find_rg_sym1a fs rgs a w i0) as [r|] eqn:H4.
  { injection H as ->. destruct (find_rg_sym1a_spec _ _ _ _ _ _ _ _ _ H4) as (A & B & C). split; [exact A | split; [exact B | left; exact C]]. }
  destruct (find_rg_symxa_spec _ _ _ _ _ _ _ _ _ H) as (A & B & C). split; [exact A | split; [exact B | right; left; exact C]].
Qed.
