(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie ExBytes.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLin AxVal AxBytes AxMem AxMemC AxZZ AxLazy AxRel AxScan.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Definition symz_whole (deep : bool) (s : store) (R : region) (f : lin) (n : Z) : option (Z * Z) :=
  if deep then (if rbetween 3 s f 0 (to_Z (rg_n R) - n) then Some (0, to_Z (rg_n R) - n) else None) else None.

Definition symz_rng (deep : bool) (s : store) (R : region) (ts : terms) (o : w64) (n : Z) : option (Z * Z) :=
  let f := lsub (wS o, ts) (wS (rg_bo R), rg_ts R) in
  match lrange s f with
  | Some (lo, hi) => if (0 <=? lo) &&& (hi + n <=? to_Z (rg_n R)) then Some (lo, hi) else symz_whole deep s R f n
  | None => symz_whole deep s R f n
  end.

Lemma symz_rng_sound (ρ : valuation) (deep : bool) (s : store) (R : region) (ts : terms) (o : w64) (n lo hi : Z) :
  sat ρ s -> symz_rng deep s R ts o n = Some (lo, hi) ->
  lo <= leval ρ (lsub (wS o, ts) (wS (rg_bo R), rg_ts R)) <= hi /\ 0 <= lo /\ hi + n <= to_Z (rg_n R).
Proof.
  intros Hs H. unfold symz_rng in H. cbv zeta in H.
  set (f := lsub (wS o, ts) (wS (rg_bo R), rg_ts R)) in *.
  assert (W : symz_whole deep s R f n = Some (lo, hi) ->
              lo <= leval ρ f <= hi /\ 0 <= lo /\ hi + n <= to_Z (rg_n R)).
  { unfold symz_whole. destruct deep; [|discriminate].
    destruct (rbetween 3 s f 0 (to_Z (rg_n R) - n)) eqn:Er; [|discriminate]. intros E. injection E as <- <-.
    pose proof (rbetween_sound ρ s 3 f _ _ Hs Er). lia. }
  destruct (lrange s f) as [[l h]|] eqn:El; [|exact (W H)].
  destruct ((0 <=? l) &&& (h + n <=? to_Z (rg_n R))) eqn:Ec; [|exact (W H)].
  injection H as <- <-. apply land_true in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  pose proof (lrange_sound ρ s f Hs _ El) as X. cbn [fst snd] in X. lia.
Qed.

(* [comment removed for export] *)
Fixpoint keys_zero0_from (d : nat) (t : itrie cell) (k : int) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match iget d t k with
           | Some c0 => cell_is0 c0 &&& keys_zero0_from d t (k + 1)%uint63 c
           | None => keys_zero0_from d t (k + 1)%uint63 c
           end
  end.

Definition rng_zero (d : nat) (t : itrie cell) (k0 k1 : Z) : bool :=
  is_empty t |||
  (if (0 <=? k0) &&& (k1 - k0 <? 4096) then keys_zero0_from d t (of_Z k0) (Z.to_nat (k1 - k0 + 1))
   else iall_key (fun k c => negb (in_keys k0 k1 k) ||| cell_is0 c) t 0 1).

Definition zero_in (R : region) (k0 k1 : Z) : Prop :=
  forall (k : int) (c : cell), k0 <= to_Z k <= k1 -> to_Z k < 2 ^ Z.of_nat (rg_d R) ->
    iget (rg_d R) (rg_cells R) k = Some c -> cell_is0 c = true.

Definition symz_fits (deep : bool) (s : store) (R : region) (ts : terms) (o : w64) (n : Z) : bool :=
  match rg_kind R with
  | KZero | KShadow =>
      match symz_rng deep s R ts o n with
      | Some (lo, hi) =>
          rng_zero (rg_d R) (rg_cells R) (lo / 8) ((hi + n - 1) / 8)
      | None => false
      end
  | _ => false
  end.

(* [comment removed for export] *)
Fixpoint keys_zero_from (d : nat) (t : itrie cell) (k : int) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match iget d t k with
           | Some c0 => cell_is0 c0 &&& keys_zero_from d t (k + 1)%uint63 c
           | None => false
           end
  end.

(* [comment removed for export] *)
Definition keys_zero (d : nat) (t : itrie cell) (k0 k1 : Z) : bool := keys_zero_from d t (of_Z k0) (Z.to_nat (k1 - k0 + 1)).

Definition symz_fits_rng (R : region) (alo ahi n : Z) : bool :=
  match rg_ts R with
  | [] =>
      let lo := alo - wZ (rg_bo R) in
      let hi := ahi - wZ (rg_bo R) in
      (0 <=? lo) &&& (hi + n <=? to_Z (rg_n R)) &&&
      match rg_kind R with
      | KZero | KShadow => rng_zero (rg_d R) (rg_cells R) (lo / 8) ((hi + n - 1) / 8)
      | KImg _ _ => keys_zero (rg_d R) (rg_cells R) (lo / 8) ((hi + n - 1) / 8)
      | _ => false
      end
  | _ => false
  end.

Definition symz_byrange (s : store) (A : list region) (v : xv) (n : nat) : option (list xb) :=
  match xrange s v with
  | Some (alo, ahi) => if (1 <=? Z.of_nat n) &&& lexists (fun R => symz_fits_rng R alo ahi (Z.of_nat n)) A then Some (repeat (BL 0%uint63) n) else None
  | None => None
  end.

(* [comment removed for export] *)
Definition symz_form (deep : bool) (s : store) (A : list region) (ts : terms) (o : w64) (n : nat) : bool :=
  (1 <=? Z.of_nat n) &&& lexists (fun R => symz_fits deep s R ts o (Z.of_nat n)) A.

(* [comment removed for export] *)
Definition a_load_symz (s : store) (A : list region) (v : xv) (n : nat) : option (list xb) :=
  match xaddr v with
  | Some (ts, o) => if symz_form false s A ts o n then Some (repeat (BL 0%uint63) n)
                    else match symz_byrange s A v n with
                         | Some l => Some l
                         | None => if symz_form true s A ts o n then Some (repeat (BL 0%uint63) n) else None
                         end
  | None => symz_byrange s A v n
  end.

Lemma symz_byrange_length (s : store) (A : list region) (v : xv) (n : nat) (l : list xb) : symz_byrange s A v n = Some l -> length l = n.
Proof.
  unfold symz_byrange. destruct (xrange s v) as [[alo ahi]|]; [|discriminate].
  destruct ((1 <=? Z.of_nat n) &&& lexists (fun R => symz_fits_rng R alo ahi (Z.of_nat n)) A); [|discriminate].
  intros H. injection H as <-. apply repeat_length.
Qed.

Lemma a_load_symz_length (s : store) (A : list region) (v : xv) (n : nat) (l : list xb) : a_load_symz s A v n = Some l -> length l = n.
Proof.
  unfold a_load_symz. destruct (xaddr v) as [[ts o]|]; [|apply symz_byrange_length].
  destruct (symz_form false s A ts o n); [intros H; injection H as <-; apply repeat_length|].
  destruct (symz_byrange s A v n) as [l0|] eqn:Eb; [intros H; injection H as <-; exact (symz_byrange_length s A v n l0 Eb)|].
  destruct (symz_form true s A ts o n); [|discriminate]. intros H. injection H as <-. apply repeat_length.
Qed.

Lemma keys_zero0_from_spec (d : nat) (t : itrie cell) : forall (cnt : nat) (k0 : Z), keys_zero0_from d t (of_Z k0) cnt = true ->
  forall k c, k0 <= k < k0 + Z.of_nat cnt -> iget d t (of_Z k) = Some c -> cell_is0 c = true.
Proof.
  induction cnt as [|cnt IH]; intros k0 H k c Hk Hg; [lia|]. cbn [keys_zero0_from] in H.
  destruct (Z.eq_dec k k0) as [->|Hne].
  - rewrite Hg in H. apply land_true in H as [Hc _]. exact Hc.
  - assert (Hr : keys_zero0_from d t (of_Z k0 + 1)%uint63 cnt = true).
    { destruct (iget d t (of_Z k0)) as [c0|]; [apply land_true in H as [_ Hr]; exact Hr | exact H]. }
    rewrite of_Z_succ in Hr. apply (IH (k0 + 1) Hr k c); [lia | exact Hg].
Qed.

Lemma rng_zero_sound (R : region) (k0 k1 : Z) : rng_zero (rg_d R) (rg_cells R) k0 k1 = true -> zero_in R k0 k1.
Proof.
  intros H k c Hk Hd Hg. unfold rng_zero in H.
  destruct (is_empty (rg_cells R)) eqn:Ee.
  { destruct (rg_cells R); try discriminate Ee. rewrite iget_empty in Hg. discriminate Hg. }
  pose proof (to_Z_bounded k) as Hkb.
  destruct ((0 <=? k0) &&& (k1 - k0 <? 4096)) eqn:Esm.
  - apply land_true in Esm as [E0 _]. apply Z.leb_le in E0.
    apply (keys_zero0_from_spec _ _ _ k0 H (to_Z k) c); [rewrite Z2Nat.id by lia; lia|]. rewrite of_to_Z. exact Hg.
  - pose proof (iall_key_iget _ (rg_d R) (rg_cells R) 0 1 _ c H Hg) as X.
    rewrite Z.mod_small in X by lia. rewrite Z.add_0_l, Z.mul_1_l in X.
    destruct (negb (in_keys k0 k1 (to_Z k))) eqn:En; [|exact X].
    exfalso. apply negb_true_iff in En. unfold in_keys in En. apply andb_false_iff in En as [E|E]; apply Z.leb_gt in E; lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma symz_core (ρ : valuation) (deep : bool) (s : store) (R : region) (ts : terms) (o : w64) (n : Z) (a : bv 64) :
  0 < n -> sat ρ s -> region_wf ρ R -> bv_unsigned a = smod ρ ts o -> symz_fits deep s R ts o n = true ->
  (rg_kind R = KZero \/ rg_kind R = KShadow) /\
  exists off lo hi, lo <= off <= hi /\ 0 <= lo /\ hi + n <= to_Z (rg_n R) /\ bv_unsigned a = rbase ρ R + off /\
    zero_in R (lo / 8) ((hi + n - 1) / 8).
Proof.
  intros Hn0 Hs Hwf Ha H. unfold symz_fits in H.
  assert (Hk : rg_kind R = KZero \/ rg_kind R = KShadow) by (destruct (rg_kind R); try discriminate; tauto).
  split; [exact Hk|].
  assert (H' : match symz_rng deep s R ts o n with
             | Some (lo, hi) =>
                 rng_zero (rg_d R) (rg_cells R) (lo / 8) ((hi + n - 1) / 8)
             | None => false end = true)
    by (destruct (rg_kind R); try discriminate; exact H).
  destruct (symz_rng deep s R ts o n) as [[lo hi]|] eqn:El; [|discriminate].
  destruct (symz_rng_sound ρ deep s R ts o n lo hi Hs El) as (Hr & E1 & E2).
  rewrite leval_lsub in Hr. unfold leval in Hr. cbn [fst snd] in Hr.
  set (off := wS o + teval ρ ts - (wS (rg_bo R) + teval ρ (rg_ts R))) in *.
  exists off, lo, hi. split; [lia|]. split; [lia|]. split; [lia|].
  split.
  - destruct Hwf as [W1 [W2 _]]. rewrite Ha.
    assert (Q1 : smod ρ ts o = (teval ρ ts + wS o) mod two64).
    { unfold smod. rewrite <- (wS_mod o). rewrite Zplus_mod_idemp_r. reflexivity. }
    assert (Q2 : rbase ρ R = (teval ρ (rg_ts R) + wS (rg_bo R)) mod two64).
    { unfold rbase, smod. rewrite <- (wS_mod (rg_bo R)). rewrite Zplus_mod_idemp_r. reflexivity. }
    rewrite Q1. rewrite Q2 in W1 |- *.
    replace (teval ρ ts + wS o) with ((teval ρ (rg_ts R) + wS (rg_bo R)) + off) by (unfold off; ring).
    rewrite Zplus_mod. rewrite (Z.mod_small off) by (unfold two64; lia).
    pose proof (Z.mod_pos_bound (teval ρ (rg_ts R) + wS (rg_bo R)) two64 ltac:(unfold two64; lia)).
    apply Z.mod_small. lia.
  - exact (rng_zero_sound R _ _ H').
Qed.

Lemma symz_bytes (ρ : valuation) (m : word -> option byte) (R : region) (lo hi n : Z) :
  RRegion segs ρ m R -> (rg_kind R = KZero \/ rg_kind R = KShadow) -> region_wf ρ R ->
  zero_in R (lo / 8) ((hi + n - 1) / 8) ->
  forall off, lo <= off -> off < hi + n -> 0 <= off < to_Z (rg_n R) -> rv segs m (wz (rbase ρ R + off)) = Some (Z_to_bv 8 0).
Proof.
  intros HR Hk Hwf Hc off Hl Hh Hoff. pose proof Hwf as [_ [H47 [Hd _]]].
  rewrite RRegion_ne in HR by (unfold is_entry; destruct Hk as [Hk|Hk]; rewrite Hk; reflexivity).
  assert (Hx : to_Z (of_Z off) = off) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2^63); lia).
  destruct (HR (of_Z off) ltac:(lia)) as [[b [Hb Hab]] _]. rewrite Hx in Hb. rewrite Hb. f_equal.
  assert (Hrb : rbyte segs R (of_Z off) = BL 0%uint63).
  { unfold rbyte, get_cell_opt. destruct (iget (rg_d R) (rg_cells R) (of_Z off >> 3)%uint63) as [c|] eqn:Ec.
    - pose proof (key_small R (of_Z off) Hd ltac:(lia)) as Hks.
      assert (X : cell_is0 c = true).
      { apply (Hc (of_Z off >> 3)%uint63 c); [|exact Hks | exact Ec]. rewrite phi_lsr3, Hx.
        split; apply Z.div_le_mono; lia. }
      apply cell_is0_byte; [exact X|]. rewrite i2n_land7, phi_land7, Hx. pose proof (Z.mod_pos_bound off 8 ltac:(lia)). lia.
    - unfold default_byte. destruct Hk as [Hk|Hk]; rewrite Hk; reflexivity. }
  rewrite Hrb in Hab. cbn [xb_z] in Hab. change (to_Z 0%uint63) with 0 in Hab. apply bv_eq. rewrite Hab. reflexivity.
Qed.

Lemma rdn_symz (ρ : valuation) (m : word -> option byte) (R : region) (lo hi : Z) (n : nat) :
  RRegion segs ρ m R -> (rg_kind R = KZero \/ rg_kind R = KShadow) -> region_wf ρ R ->
  zero_in R (lo / 8) ((hi + Z.of_nat n - 1) / 8) ->
  forall k off, lo <= off -> off + Z.of_nat k <= hi + Z.of_nat n -> (k <= n)%nat -> off + Z.of_nat k <= to_Z (rg_n R) -> 0 <= off ->
  rdn segs m (wz (rbase ρ R + off)) k = Some (repeat (Z_to_bv 8 0) k).
Proof.
  intros HR Hk Hwf Hc. induction k as [|k IH]; intros off Hl Hh Hkn Hn H0; [reflexivity|].
  cbn [rdn repeat]. pose proof (symz_bytes ρ m R lo hi (Z.of_nat n) HR Hk Hwf Hc off Hl ltac:(lia) ltac:(lia)) as Hb.
  unfold rv in Hb. rewrite Hb. rewrite wz_succ. rewrite <- Z.add_assoc. rewrite IH by lia. reflexivity.
Qed.

Lemma rdn_zeros_symz (m : word -> option byte) : forall (k : nat) (a : Z),
  (forall j, (j < k)%nat -> rv segs m (wz (a + Z.of_nat j)) = Some (Z_to_bv 8 0)) -> rdn segs m (wz a) k = Some (repeat (Z_to_bv 8 0) k).
Proof.
  induction k as [|k IH]; intros a H; [reflexivity|]. cbn [rdn repeat].
  pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rv in H0. rewrite H0. rewrite wz_succ.
  rewrite (IH (a + 1)); [reflexivity|]. intros j Hj. replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. apply H. lia.
Qed.

Lemma keys_zero_from_spec (d : nat) (t : itrie cell) : forall (cnt : nat) (k0 : Z), keys_zero_from d t (of_Z k0) cnt = true ->
  forall k, k0 <= k < k0 + Z.of_nat cnt -> exists c, iget d t (of_Z k) = Some c /\ cell_is0 c = true.
Proof.
  induction cnt as [|cnt IH]; intros k0 H k Hk; [lia|]. cbn [keys_zero_from] in H.
  destruct (iget d t (of_Z k0)) as [c0|] eqn:Eg; [|discriminate H]. apply land_true in H as [Hc Hr].
  destruct (Z.eq_dec k k0) as [->|Hne]; [exists c0; split; [exact Eg | exact Hc]|].
  rewrite of_Z_succ in Hr. apply (IH (k0 + 1) Hr k). lia.
Qed.

Lemma keys_zero_spec (d : nat) (t : itrie cell) (k0 k1 : Z) : keys_zero d t k0 k1 = true ->
  forall k, k0 <= k <= k1 -> exists c, iget d t (of_Z k) = Some c /\ cell_is0 c = true.
Proof. intros H k Hk. apply (keys_zero_from_spec d t _ k0 H k). lia. Qed.

Lemma symz_rng_bytes (ρ : valuation) (m : word -> option byte) (R : region) (alo ahi n : Z) :
  RRegion segs ρ m R -> region_wf ρ R -> symz_fits_rng R alo ahi n = true ->
  forall off, alo - wZ (rg_bo R) <= off -> off < ahi - wZ (rg_bo R) + n -> rv segs m (wz (rbase ρ R + off)) = Some (Z_to_bv 8 0).
Proof.
  intros HR Hwf H off Hl Hh. unfold symz_fits_rng in H. destruct (rg_ts R) as [|p ts'] eqn:Ets; [|discriminate].
  destruct (0 <=? alo - wZ (rg_bo R)) eqn:E1; [|discriminate]. destruct (ahi - wZ (rg_bo R) + n <=? to_Z (rg_n R)) eqn:E2; [|discriminate].
  apply Z.leb_le in E1. apply Z.leb_le in E2.
  destruct (rg_kind R) as [| | |wr j|ph] eqn:Ek; try discriminate.
  - exact (symz_bytes ρ m R (alo - wZ (rg_bo R)) (ahi - wZ (rg_bo R)) n HR (or_introl Ek) Hwf
             (rng_zero_sound R _ _ H) off Hl Hh ltac:(lia)).
  - exact (symz_bytes ρ m R (alo - wZ (rg_bo R)) (ahi - wZ (rg_bo R)) n HR (or_intror Ek) Hwf
             (rng_zero_sound R _ _ H) off Hl Hh ltac:(lia)).
  - pose proof Hwf as [_ [H47 [Hd _]]].
    rewrite RRegion_ne in HR by (unfold is_entry; rewrite Ek; reflexivity).
    assert (Hx : to_Z (of_Z off) = off) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2^63); lia).
    destruct (HR (of_Z off) ltac:(lia)) as [[b [Hb Hab]] _]. rewrite Hx in Hb. rewrite Hb. f_equal.
    destruct (keys_zero_spec _ _ _ _ H (off / 8) ltac:(split; apply Z.div_le_mono; lia)) as [c [Ec Hc0]].
    assert (Ek8 : (of_Z off >> 3)%uint63 = of_Z (off / 8)).
    { apply to_Z_inj. rewrite phi_lsr3, Hx, of_Z_spec. symmetry. apply Z.mod_small. change wB with (2^63).
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (Hrb : rbyte segs R (of_Z off) = BL 0%uint63).
    { unfold rbyte, get_cell_opt. rewrite Ek8, Ec. apply cell_is0_byte; [exact Hc0|].
      rewrite i2n_land7, phi_land7, Hx. pose proof (Z.mod_pos_bound off 8 ltac:(lia)). lia. }
    rewrite Hrb in Hab. cbn [xb_z] in Hab. change (to_Z 0%uint63) with 0 in Hab. apply bv_eq. rewrite Hab. reflexivity.
Qed.

Lemma symz_byrange_sound (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) (v : xv) (a : bv 64) (n : nat) (l : list xb) :
  sat ρ s -> RMem segs ρ A m -> xv_val ρ v a -> symz_byrange s A v n = Some l ->
  exists bs, rdn segs m a n = Some bs /\ Forall2 (xb_bv ρ) l bs.
Proof.
  intros Hs HM Hv H. unfold symz_byrange in H.
  destruct (xrange s v) as [[alo ahi]|] eqn:Er; [|discriminate].
  destruct (1 <=? Z.of_nat n) eqn:En; [|discriminate]. apply Z.leb_le in En.
  destruct (lexists (fun R => symz_fits_rng R alo ahi (Z.of_nat n)) A) eqn:Ez; [|discriminate]. injection H as <-.
  apply lexists_exists in Ez as [R [HIn Hz]].
  pose proof (xrange_sound ρ s v a Hs Hv _ Er) as Hra. cbn [fst snd] in Hra.
  destruct HM as [Hok HR]. rewrite Forall_forall in HR. pose proof (HR R HIn) as HRR.
  assert (Hwf : region_wf ρ R).
  { clear -Hok HIn. induction A as [|R0 A' IH]; [destruct HIn|]. destruct Hok as [W [_ Hok']].
    destruct HIn as [<-|HIn]; [exact W | apply IH; assumption]. }
  assert (Hts : rg_ts R = []) by (unfold symz_fits_rng in Hz; destruct (rg_ts R); [reflexivity | discriminate]).
  assert (Hrb : rbase ρ R = wZ (rg_bo R)).
  { unfold rbase, smod. rewrite Hts. cbn [teval]. rewrite Z.add_0_l. apply Z.mod_small. apply wZ_range. }
  assert (Hfit : 0 <= alo - wZ (rg_bo R) /\ ahi - wZ (rg_bo R) + Z.of_nat n <= to_Z (rg_n R)).
  { unfold symz_fits_rng in Hz. rewrite Hts in Hz.
    destruct (0 <=? alo - wZ (rg_bo R)) eqn:E1; [|discriminate]. destruct (ahi - wZ (rg_bo R) + Z.of_nat n <=? to_Z (rg_n R)) eqn:E2; [|discriminate].
    apply Z.leb_le in E1. apply Z.leb_le in E2. lia. }
  exists (repeat (Z_to_bv 8 0) n). split.
  - set (off := bv_unsigned a - wZ (rg_bo R)).
    replace a with (wz (rbase ρ R + off)) by (apply bv_eq; rewrite u_wz; [unfold off; lia | pose proof (bvu_range a); unfold two64 in *; unfold off; lia]).
    apply rdn_zeros_symz. intros j Hj. rewrite <- Z.add_assoc.
    apply (symz_rng_bytes ρ m R alo ahi (Z.of_nat n) HRR Hwf Hz); unfold off; lia.
  - clear. induction n as [|n IH]; cbn [repeat]; constructor; [|exact IH]. unfold xb_bv. cbn [xb_z]. reflexivity.
Qed.

Lemma symz_form_sound (ρ : valuation) (deep : bool) (s : store) (A : list region) (m : word -> option byte) (v : xv) (a : bv 64)
    (ts : terms) (o : w64) (n : nat) :
  sat ρ s -> RMem segs ρ A m -> xv_val ρ v a -> xaddr v = Some (ts, o) -> symz_form deep s A ts o n = true ->
  exists bs, rdn segs m a n = Some bs /\ Forall2 (xb_bv ρ) (repeat (BL 0%uint63) n) bs.
Proof.
  intros Hs HM Hv Ea Ec. unfold symz_form in Ec.
  apply land_true in Ec as [En Ez]. apply Z.leb_le in En.
  apply lexists_exists in Ez as [R [HIn Hz]].
  destruct HM as [Hok HR]. rewrite Forall_forall in HR. pose proof (HR R HIn) as HRR.
  assert (Hwf : region_wf ρ R).
  { clear -Hok HIn. induction A as [|R0 A' IH]; [destruct HIn|]. destruct Hok as [W [_ Hok']].
    destruct HIn as [<-|HIn]; [exact W | apply IH; assumption]. }
  destruct (symz_core ρ deep s R ts o (Z.of_nat n) a ltac:(lia) Hs Hwf (xaddr_val ρ v a ts o Hv Ea) Hz) as [Hk [off [lo [hi [Hoff [H0 [H1 [Ha Hc]]]]]]]].
  exists (repeat (Z_to_bv 8 0) n). split.
  - replace a with (wz (rbase ρ R + off)) by (apply bv_eq; rewrite u_wz; [lia | destruct Hwf as [W1 _]; unfold two64 in *; pose proof (smod_range ρ (rg_ts R) (rg_bo R)); unfold rbase in *; lia]).
    apply (rdn_symz ρ m R lo hi n HRR Hk Hwf Hc n off); lia.
  - clear. induction n as [|n IH]; cbn [repeat]; constructor; [|exact IH]. unfold xb_bv. cbn [xb_z]. reflexivity.
Qed.

Theorem a_load_symz_sound (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) (v : xv) (a : bv 64) (n : nat) (l : list xb) :
  sat ρ s -> RMem segs ρ A m -> xv_val ρ v a -> a_load_symz s A v n = Some l ->
  exists bs, rdn segs m a n = Some bs /\ Forall2 (xb_bv ρ) l bs.
Proof.
  intros Hs HM Hv H. unfold a_load_symz in H. destruct (xaddr v) as [[ts o]|] eqn:Ea; [|exact (symz_byrange_sound ρ s A m v a n l Hs HM Hv H)].
  destruct (symz_form false s A ts o n) eqn:E1; [injection H as <-; exact (symz_form_sound ρ false s A m v a ts o n Hs HM Hv Ea E1)|].
  destruct (symz_byrange s A v n) as [l0|] eqn:Eb; [injection H as <-; exact (symz_byrange_sound ρ s A m v a n l0 Hs HM Hv Eb)|].
  destruct (symz_form true s A ts o n) eqn:E2; [|discriminate]. injection H as <-.
  exact (symz_form_sound ρ true s A m v a ts o n Hs HM Hv Ea E2).
Qed.

End WithSegs.
