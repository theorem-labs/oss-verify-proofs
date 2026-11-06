(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnDivCorrect BnDivLoop BnInv BnSpecs BnSpecs2 BnAddSpec BnDivSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgArith BgInv BgSpecs BgLibSpec BgShiftSpec BgAddSpec BgWordSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section DivSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Lemma live_refs_true : forall (s : ST) rs, Forall (fun r => live r s) rs -> live_refs (st_ctx s) rs = true.
Proof.
  intros s rs H. unfold live_refs. apply forallb_forall. intros r Hin.
  rewrite Forall_forall in H. apply Nat.ltb_lt. exact (H r Hin).
Qed.

Lemma hoareG_live : forall {A} rs (k : BM (M:=btree ptr) (ptr:=ptr) A) F F' s Q,
  Forall (fun r => live r s) rs -> hoareG F F' s k Q -> hoareG F F' s (bn_live ops rs k) Q.
Proof.
  intros A rs k F F' s Q HL H X Hs Hf Ho. unfold bn_live, bbind, bgetctx. cbn [bind ret tree_ops tbind fst snd].
  rewrite (live_refs_true s rs HL). apply H; assumption.
Qed.

Lemma hoare_live : forall {A} rs (k : BM (M:=btree ptr) (ptr:=ptr) A) F s Q,
  Forall (fun r => live r s) rs -> hoare F s k Q -> hoare F s (bn_live ops rs k) Q.
Proof. intros. apply hoareG_live; assumption. Qed.

Lemma bn_left_align_spec : forall r F s,
  (r < length (st_bns s))%nat -> r <> ROne -> bn_norm (getbn r s) -> (1 <= bn_top (getbn r s))%nat ->
  hoare F s (bn_left_align ops r) (fun sh s' => exists b', s' = setbn r b' s /\
     0 <= sh < 64 /\ bn_top b' = bn_top (getbn r s) /\ bn_neg b' = bn_neg (getbn r s) /\
     bn_mag b' = bn_mag (getbn r s) * 2 ^ sh /\ 2 ^ 63 <= nth (bn_top (getbn r s) - 1) (bn_buf b') 0).
Proof.
  intros r F s Hr Hn Hnorm Htop. apply hoare_wf. intros Hs. unfold bn_left_align. apply hoare_bind_get.
  set (b := getbn r s) in *. pose proof (st_wf_ok r s Hs Hr Hn) as Hb. fold b in Hb.
  destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4). unfold bn_dmax in *.
  set (l := firstn (bn_top b) (bn_buf b)).
  assert (Hl : limbs l) by (apply limbs_firstn; exact Hb1).
  assert (Hll : length l = bn_top b) by (apply firstn_length_le; lia).
  assert (Ent : nth (bn_top b - 1) l 0 = nth (bn_top b - 1) (bn_buf b) 0).
  { subst l. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top b - 1) (bn_top b)); [reflexivity|lia]. }
  destruct Hnorm as [Hnorm|Hnorm]; [lia|].
  pose proof (left_align_value l Hl ltac:(lia) ltac:(rewrite Hll, Ent; exact Hnorm)) as Hla. cbv zeta in Hla.
  rewrite Hll, Ent in Hla. destruct Hla as (L1 & L2 & L3 & L4 & L5).
  set (sh := 64 - num_bits_word (nth (bn_top b - 1) (bn_buf b) 0)) in *.
  set (rl := fst (lshift_limbs l sh 0)) in *.
  set (b' := bn_with_buf b (splice (bn_buf b) 0 rl)).
  assert (Hlen : length (bn_buf b') = length (bn_buf b)) by (subst b'; cbn [bn_with_buf bn_buf]; apply splice_length; lia).
  assert (Hfn : firstn (bn_top b) (bn_buf b') = rl) by (subst b'; cbn [bn_with_buf bn_buf]; apply firstn_splice_0; lia).
  assert (Hb' : bg_ok b').
  { unfold bg_ok, bn_dmax. rewrite Hlen. subst b'. cbn [bn_with_buf bn_buf bn_top bn_flags].
    split; [apply splice_limbs; assumption|]. tauto. }
  apply hoare_bind_set; try assumption; try reflexivity.
  apply hoare_ret. exists b'. split; [reflexivity|]. split; [exact L1|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - unfold bn_mag. change (bn_top b') with (bn_top b). rewrite Hfn. exact L4.
  - assert (E : nth (bn_top b - 1) (bn_buf b') 0 = nth (bn_top b - 1) rl 0).
    { rewrite <- Hfn. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top b - 1) (bn_top b)); [reflexivity|lia]. }
    rewrite E. exact L5.
Qed.

Definition div_core (res tmp snum sdiv : bnref) (rm : option bnref) (num divisor : bnref) : BM (M:=btree ptr) (ptr:=ptr) unit :=
  bbind ops (BN_copy ops sdiv divisor) (fun _ =>
  bbind ops (bn_left_align ops sdiv) (fun norm_shift =>
  bbind ops (bbind ops (bget ops sdiv) (fun b => bset ops sdiv (bn_with_neg b false))) (fun _ =>
  bbind ops (bn_lshift_fixed_top ops snum num norm_shift) (fun _ =>
  bbind ops (bget ops sdiv) (fun sd =>
  bbind ops (bget ops snum) (fun sn =>
  let div_n := bn_top sd in
  bbind ops (if (bn_top sn <=? div_n)%nat then
     bbind ops (bn_wexpand ops snum (div_n + 1)) (fun _ =>
     bbind ops (bget ops snum) (fun sn' =>
     bset ops snum (mkBN (bn_d sn') (splice (bn_buf sn') (bn_top sn) (repeat 0 (div_n - bn_top sn + 1)))
                     (div_n + 1) (bn_neg sn') (bn_flags sn'))))
   else bret ops tt) (fun _ =>
  bbind ops (bget ops snum) (fun sn =>
  let num_n := bn_top sn in
  let loop := (num_n - div_n)%nat in
  let d0 := nth (div_n - 1) (bn_buf sd) 0 in
  let d1 := if (div_n =? 1)%nat then 0 else nth (div_n - 2) (bn_buf sd) 0 in
  bbind ops (bn_wexpand ops res loop) (fun _ =>
  bbind ops (bget ops num) (fun nm =>
  bbind ops (bget ops divisor) (fun dvs =>
  let num_neg := bn_neg nm in
  bbind ops (bbind ops (bget ops res) (fun r => bset ops res (mkBN (bn_d r) (bn_buf r) loop (xorb num_neg (bn_neg dvs)) (bn_flags r)))) (fun _ =>
  bbind ops (bn_wexpand ops tmp (div_n + 1)) (fun _ =>
  bbind ops (bget ops snum) (fun sn =>
  bbind ops (bget ops tmp) (fun tm =>
  bbind ops (bget ops res) (fun r =>
  let '(snb, tmb, rb) := div_loop (bn_buf sd) div_n loop num_n d0 d1 loop 0 (bn_buf sn, bn_buf tm, bn_buf r) in
  bbind ops (bset ops tmp (bn_with_buf tm tmb)) (fun _ =>
  bbind ops (bset ops res (bn_with_buf r rb)) (fun _ =>
  bbind ops (bset ops snum (mkBN (bn_d sn) snb div_n num_neg (bn_flags sn))) (fun _ =>
  bbind ops (match rm with Some r => bn_rshift_fixed_top ops r snum norm_shift | None => bret ops tt end) (fun _ =>
  BN_CTX_end ops)))))))))))))))))))).

Lemma bn_div_fixed_top_unfold : forall dv rm num divisor,
  bn_div_fixed_top ops dv rm num divisor =
  bn_live ops (num :: divisor :: opt_refs dv ++ opt_refs rm) (
  bbind ops (BN_CTX_start ops) (fun _ =>
  bbind ops (match dv with None => BN_CTX_get ops | Some r => bret ops r end) (fun res =>
  bbind ops (BN_CTX_get ops) (fun tmp =>
  bbind ops (BN_CTX_get ops) (fun snum =>
  bbind ops (BN_CTX_get ops) (fun sdiv => div_core res tmp snum sdiv rm num divisor)))))).
Proof. reflexivity. Qed.

Definition div_fix_post (res : bnref) (rm : option bnref) (num0 div0 : BN) (s' : ST) : Prop :=
  let q := getbn res s' in
  bn_mag q = bn_mag num0 / bn_mag div0 /\ bn_neg q = xorb (bn_neg num0) (bn_neg div0) /\
  Z.of_nat (bn_top q) + Z.of_nat (bn_top div0) = Z.max (Z.of_nat (bn_top num0) + 1) (Z.of_nat (bn_top div0) + 1) /\
  (forall r, rm = Some r -> let x := getbn r s' in
     bn_mag x = bn_mag num0 mod bn_mag div0 /\ bn_neg x = bn_neg num0 /\ bn_top x = bn_top div0).

Definition ndiff (a b : bnref) : Prop := a <> b.
Lemma ndiff_sym : forall a b, ndiff a b -> b <> a.
Proof. intros a b H E. apply H. symmetry. exact E. Qed.

Ltac gso := rewrite ?getbn_setbn_other by (first [assumption | apply ndiff_sym; assumption]).

Lemma div_core_spec : forall res tmp snum sdiv rm num divisor fr fp F s,
  (res < length (st_bns s))%nat -> (tmp < length (st_bns s))%nat -> (snum < length (st_bns s))%nat ->
  (sdiv < length (st_bns s))%nat -> (num < length (st_bns s))%nat -> (divisor < length (st_bns s))%nat ->
  ndiff res ROne -> ndiff tmp ROne -> ndiff snum ROne -> ndiff sdiv ROne ->
  (forall r, rm = Some r -> (r < length (st_bns s))%nat /\ ndiff r ROne /\ ndiff r res /\ ndiff r tmp /\ ndiff r snum /\ ndiff r sdiv /\ ndiff r divisor) ->
  ndiff tmp snum -> ndiff tmp sdiv -> ndiff snum sdiv -> ndiff res tmp -> ndiff res snum -> ndiff res sdiv -> ndiff res divisor ->
  ndiff num tmp -> ndiff num snum -> ndiff num sdiv -> ndiff divisor tmp -> ndiff divisor snum -> ndiff divisor sdiv ->
  gx_frames (st_ctx s) = fr ++ [fp] ->
  bn_norm (getbn divisor s) -> (1 <= bn_top (getbn divisor s))%nat ->
  Z.of_nat (bn_top (getbn num s)) + 2 <= BG_DMAX -> Z.of_nat (bn_top (getbn divisor s)) + 2 <= BG_DMAX ->
  hoare F s (div_core res tmp snum sdiv rm num divisor) (fun _ s' =>
     length (st_bns s') = length (st_bns s) /\ scal_same s s' /\ gx_used (st_ctx s') = fp /\ gx_frames (st_ctx s') = fr /\
     (forall x, ndiff x res -> ndiff x tmp -> ndiff x snum -> ndiff x sdiv -> rm <> Some x -> getbn x s' = getbn x s) /\
     div_fix_post res rm (getbn num s) (getbn divisor s) s').
Proof.
  intros res tmp snum sdiv rm num divisor fr fp F s Vres Vtmp Vsnum Vsdiv Vnum Vdiv Nres Ntmp Nsnum Nsdiv Hrm
         D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 Hfr Hn2 Htop2 Ht1 Ht2.
  apply hoare_wf. intros Hs. unfold div_core.
  set (b1 := getbn num s) in *. set (b2 := getbn divisor s) in *.
  pose proof (st_wf_okv num s Hs Vnum) as Hb1. fold b1 in Hb1.
  pose proof (st_wf_okv divisor s Hs Vdiv) as Hb2. fold b2 in Hb2.

  eapply hoare_bind; [apply BN_copy_spec; assumption|].
  intros [] s1 Hs1 (sd1 & -> & Etop1 & Eneg1 & Efn1). fold b2 in Etop1, Eneg1, Efn1.
  assert (Hmag1 : bn_mag sd1 = bn_mag b2) by (apply mag_of_firstn_eq; assumption).
  assert (Hnorm1 : bn_norm sd1) by (eapply norm_of_firstn_eq; eassumption).

  eapply hoare_bind; [apply bn_left_align_spec; [rewrite length_setbn; exact Vsdiv|exact Nsdiv|
                        rewrite getbn_setbn_same by exact Vsdiv; exact Hnorm1|rewrite getbn_setbn_same by exact Vsdiv; lia]|].
  intros sh s2 Hs2 (sd2 & -> & Hsh & Etop2 & Eneg2 & Emag2 & Hd0). rewrite getbn_setbn_same in Etop2, Eneg2, Emag2, Hd0 by exact Vsdiv.
  rewrite setbn_setbn_same in Hs2 |- *.
  pose proof (st_wf_ok sdiv _ Hs2 ltac:(rewrite length_setbn; exact Vsdiv) Nsdiv) as Hsd2. rewrite getbn_setbn_same in Hsd2 by exact Vsdiv.

  set (sd3 := bn_with_neg sd2 false).
  assert (Hsd3 : bg_ok sd3) by (destruct Hsd2 as (A1 & A2 & A3 & A4); unfold bg_ok, bn_dmax in *; subst sd3; cbn [bn_with_neg bn_buf bn_top bn_flags]; tauto).
  apply hoare_bind_update; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Vsdiv; try assumption; try reflexivity.
  rewrite setbn_setbn_same. fold sd3. set (s3 := setbn sdiv sd3 s).
  assert (L3 : length (st_bns s3) = length (st_bns s)) by (subst s3; apply length_setbn).
  assert (Eb1_3 : getbn num s3 = b1) by (subst s3; gso; reflexivity).

  eapply hoare_bind; [apply bn_lshift_fixed_top_spec; try rewrite L3; try assumption; try lia|].
  { rewrite Eb1_3. rewrite Z.div_small by lia. lia. }
  intros [] s4 Hs4 (sn1 & -> & Etsn1 & Ensn1 & Emsn1). rewrite Eb1_3 in Etsn1, Ensn1, Emsn1.
  rewrite Z.div_small in Etsn1 by lia. cbn [Z.to_nat] in Etsn1. rewrite Nat.add_0_r in Etsn1.
  set (s4 := setbn snum sn1 s3) in *.
  assert (L4 : length (st_bns s4) = length (st_bns s)) by (subst s4; rewrite length_setbn; exact L3).
  pose proof (st_wf_ok snum _ Hs4 ltac:(rewrite L4; exact Vsnum) Nsnum) as Hsn1.
  assert (Eg2 : getbn sdiv s4 = sd3) by (subst s4 s3; gso; apply getbn_setbn_same; exact Vsdiv).
  assert (Eg1 : getbn snum s4 = sn1) by (subst s4; apply getbn_setbn_same; rewrite L3; exact Vsnum).
  rewrite Eg1 in Hsn1.
  apply hoare_bind_get. apply hoare_bind_get. rewrite Eg2, Eg1.
  change (bn_top sd3) with (bn_top sd2). rewrite Etop2, Etop1. set (div_n := bn_top b2) in *.

  eapply hoare_bind with (R := fun _ s5 => exists sn2, s5 = setbn snum sn2 s3 /\ bg_ok sn2 /\
                                  bn_mag sn2 = bn_mag b1 * 2 ^ sh /\ bn_top sn2 = Nat.max (bn_top b1 + 1) (div_n + 1)).
  { destruct (Nat.leb_spec (bn_top sn1) div_n) as [Hle|Hgt].
    - eapply hoare_bind; [apply bn_wexpand_spec; [rewrite L4; exact Vsnum|exact Nsnum|unfold div_n; lia]|].
      intros [] s5 Hs5 (sn' & -> & Hexp). rewrite Eg1 in Hexp. destruct Hexp as (E1 & E2 & E3 & E4 & Hsn' & E5 & E6).
      subst s4. rewrite setbn_setbn_same in Hs5 |- *.
      apply hoare_bind_get. rewrite getbn_setbn_same by (rewrite L3; exact Vsnum).
      destruct Hsn' as (A1 & A2 & A3 & A4). destruct Hsn1 as (B1 & B2 & B3 & B4). unfold bn_dmax in *.
      set (k := (div_n - bn_top sn1 + 1)%nat).
      assert (Hk : (bn_top sn1 + k = div_n + 1)%nat) by lia.
      set (sn2 := mkBN (bn_d sn') (splice (bn_buf sn') (bn_top sn1) (repeat 0 k)) (div_n + 1) (bn_neg sn') (bn_flags sn')).
      assert (L2 : length (bn_buf sn2) = length (bn_buf sn')).
      { subst sn2. cbn [bn_buf]. apply splice_length. rewrite repeat_length. lia. }
      assert (Hsn2 : bg_ok sn2).
      { unfold bg_ok, bn_dmax. rewrite L2. subst sn2. cbn [bn_buf bn_top bn_flags].
        split; [apply splice_limbs; [exact A1|apply limbs_repeat; exact limb_0]|]. repeat split; try assumption; lia. }
      eapply hoare_set; try rewrite length_setbn; try rewrite getbn_setbn_same by (rewrite L3; exact Vsnum); try rewrite L3; try assumption; try reflexivity.
      rewrite setbn_setbn_same. exists sn2. split; [reflexivity|]. split; [exact Hsn2|]. split.
      + unfold bn_mag at 1. subst sn2. cbn [bn_buf bn_top]. rewrite <- Hk, firstn_pad_zeros by lia.
        rewrite lval_app, lval_repeat0, Z.mul_0_r, Z.add_0_r. rewrite <- Emsn1. unfold bn_mag.
        rewrite E4. destruct (Nat.leb_spec (div_n + 1) (length (bn_buf sn1))) as [Hfit|Hnf].
        * reflexivity.
        * rewrite firstn_app, firstn_firstn, Nat.min_id. rewrite firstn_length_le by lia.
          rewrite Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. reflexivity.
      + subst sn2. cbn [bn_top]. lia.
    - apply hoare_ret. exists sn1. split; [reflexivity|]. split; [exact Hsn1|]. split; [exact Emsn1|lia]. }
  intros [] s5 Hs5 (sn2 & -> & Hsn2 & Emsn2 & Etsn2).
  set (s5 := setbn snum sn2 s3) in *.
  assert (L5 : length (st_bns s5) = length (st_bns s)) by (subst s5; rewrite length_setbn; exact L3).
  assert (Eg1_5 : getbn snum s5 = sn2) by (subst s5; apply getbn_setbn_same; rewrite L3; exact Vsnum).
  assert (Eg2_5 : getbn sdiv s5 = sd3) by (subst s5 s3; gso; apply getbn_setbn_same; exact Vsdiv).
  assert (Eb1_5 : getbn num s5 = b1) by (subst s5 s3; gso; reflexivity).
  assert (Eb2_5 : getbn divisor s5 = b2) by (subst s5 s3; gso; reflexivity).
  apply hoare_bind_get. rewrite Eg1_5. rewrite Etsn2.
  set (num_n := Nat.max (bn_top b1 + 1) (div_n + 1)) in *.
  set (loop := (num_n - div_n)%nat).
  assert (Hloop : (1 <= loop)%nat /\ num_n = (loop + div_n)%nat) by (subst loop num_n; lia).

  eapply hoare_bind; [apply bn_wexpand_spec; [rewrite L5; exact Vres|exact Nres|subst loop num_n div_n; lia]|].
  intros [] s6 Hs6 (q1 & -> & Hexp6). destruct Hexp6 as (Q1 & Q2 & Q3 & Q4 & Hq1 & Q5 & Q6).
  set (s6 := setbn res q1 s5) in *.
  assert (L6 : length (st_bns s6) = length (st_bns s)) by (subst s6; rewrite length_setbn; exact L5).
  apply hoare_bind_get. apply hoare_bind_get.
  assert (Eneg_num : bn_neg (getbn num s6) = bn_neg b1).
  { subst s6. destruct (Nat.eq_dec res num) as [E|E].
    - subst num. rewrite getbn_setbn_same by (rewrite L5; exact Vres). rewrite Q2, Eb1_5. reflexivity.
    - rewrite getbn_setbn_other by exact E. rewrite Eb1_5. reflexivity. }
  assert (Eg_b2 : getbn divisor s6 = b2) by (subst s6; gso; exact Eb2_5).
  rewrite Eneg_num, Eg_b2.
  set (q2 := mkBN (bn_d q1) (bn_buf q1) loop (xorb (bn_neg b1) (bn_neg b2)) (bn_flags q1)).
  assert (Hq2 : bg_ok q2).
  { destruct Hq1 as (A1 & A2 & A3 & A4). unfold bg_ok, bn_dmax in *. subst q2. cbn [bn_buf bn_top bn_flags]. repeat split; try assumption; lia. }
  apply hoare_bind_update; try rewrite L6; try (unfold s6; rewrite getbn_setbn_same by (rewrite L5; exact Vres)); try assumption; try reflexivity.
  unfold s6. rewrite setbn_setbn_same. fold q2. set (s7 := setbn res q2 s5).
  assert (L7 : length (st_bns s7) = length (st_bns s)) by (subst s7; rewrite length_setbn; exact L5).

  eapply hoare_bind; [apply bn_wexpand_spec; [rewrite L7; exact Vtmp|exact Ntmp|subst div_n; lia]|].
  intros [] s8 Hs8 (tm1 & -> & Hexp8). destruct Hexp8 as (T1 & T2 & T3 & T4 & Htm1 & T5 & T6).
  set (s8 := setbn tmp tm1 s7) in *.
  assert (L8 : length (st_bns s8) = length (st_bns s)) by (subst s8; rewrite length_setbn; exact L7).
  apply hoare_bind_get. apply hoare_bind_get. apply hoare_bind_get.
  assert (Eg1_8 : getbn snum s8 = sn2) by (subst s8 s7; gso; exact Eg1_5).
  assert (Eg0_8 : getbn tmp s8 = tm1) by (subst s8; apply getbn_setbn_same; rewrite L7; exact Vtmp).
  assert (Eg3_8 : getbn res s8 = q2) by (subst s8 s7; gso; apply getbn_setbn_same; rewrite L5; exact Vres).
  rewrite Eg1_8, Eg0_8, Eg3_8.

  destruct Hsn2 as (N1 & N2 & N3 & N4). destruct Htm1 as (M1 & M2 & M3 & M4). destruct Hq1 as (R1 & R2 & R3 & R4).
  destruct Hsd2 as (P1 & P2 & P3 & P4). unfold bn_dmax in *.
  assert (Hd0' : nth (div_n - 1) (bn_buf sd3) 0 = nth (div_n - 1) (bn_buf sd2) 0) by reflexivity.
  assert (Hvge : Bp (div_n - 1) * 2 ^ 63 <= lval (firstn div_n (bn_buf sd3))).
  { change (bn_buf sd3) with (bn_buf sd2).
    set (l := firstn div_n (bn_buf sd2)). assert (Hl : limbs l) by (apply limbs_firstn; exact P1).
    assert (Hll : length l = div_n) by (apply firstn_length_le; lia).
    pose proof (nth_limb_val l (div_n - 1) Hl ltac:(lia)) as E.
    assert (En : nth (div_n - 1) l 0 = nth (div_n - 1) (bn_buf sd2) 0).
    { subst l. rewrite nth_firstn. destruct (Nat.ltb_spec (div_n - 1) div_n); [reflexivity|lia]. }
    rewrite En in E. rewrite Etop1 in Hd0. fold div_n in Hd0.
    pose proof (lval_nonneg _ (limbs_firstn (div_n - 1) l Hl)). pose proof (lval_nonneg _ (limbs_skipn (S (div_n - 1)) l Hl)).
    pose proof (Bp_pos (div_n - 1)). pose proof (Bp_pos (S (div_n - 1))). nia. }
  assert (HN0 : lval (firstn num_n (bn_buf sn2)) = bn_mag b1 * 2 ^ sh) by (rewrite <- Emsn2; unfold bn_mag; rewrite Etsn2; reflexivity).
  assert (Htopc : lval (slice (bn_buf sn2) loop div_n) < lval (firstn div_n (bn_buf sd3))).
  { apply (div_top_cond (bn_buf sn2) loop div_n (bn_top b1)); try assumption; try lia.
    destruct Hloop as [_ El]. rewrite <- El, HN0.
    pose proof (okv_mag_lt b1 Hb1). pose proof (okv_mag_nonneg b1 Hb1).
    assert (2 ^ sh <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
    assert (0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia). pose proof (Bp_pos (bn_top b1)). nia. }
  pose proof (div_loop_spec (bn_buf sd3) div_n loop num_n (nth (div_n - 1) (bn_buf sd3) 0)
                (if (div_n =? 1)%nat then 0 else nth (div_n - 2) (bn_buf sd3) 0)
                P1 ltac:(lia) ltac:(change (bn_buf sd3) with (bn_buf sd2); lia) (proj2 Hloop) eq_refl eq_refl
                ltac:(rewrite Hd0'; rewrite Etop1 in Hd0; exact Hd0)
                (bn_buf sn2) (bn_buf tm1) (bn_buf q2) N1 M1 R1 ltac:(lia) ltac:(lia) ltac:(subst q2; cbn [bn_buf]; lia) Htopc) as Hloopspec.
  cbv zeta in Hloopspec.
  destruct (div_loop (bn_buf sd3) div_n loop num_n _ _ loop 0 (bn_buf sn2, bn_buf tm1, bn_buf q2)) as [[snb tmb] rb].
  destruct Hloopspec as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
  rewrite HN0 in K7, K8.

  apply hoare_bind_set; try rewrite L8; try rewrite Eg0_8; try assumption; try reflexivity.
  { unfold bg_ok, bn_dmax. cbn [bn_with_buf bn_buf bn_top bn_flags]. rewrite K4. repeat split; try assumption; lia. }
  set (s9 := setbn tmp (bn_with_buf tm1 tmb) s8).
  assert (L9 : length (st_bns s9) = length (st_bns s)) by (subst s9; rewrite length_setbn; exact L8).
  assert (Eg3_9 : getbn res s9 = q2) by (subst s9; gso; exact Eg3_8).
  set (q3 := bn_with_buf q2 rb).
  assert (Hq3 : bg_ok q3).
  { unfold bg_ok, bn_dmax. subst q3 q2. cbn [bn_with_buf bn_buf bn_top bn_flags] in *. rewrite K6. repeat split; try assumption; lia. }
  apply hoare_bind_set; try rewrite L9; try rewrite Eg3_9; try assumption; try reflexivity.
  set (s10 := setbn res q3 s9).
  assert (L10 : length (st_bns s10) = length (st_bns s)) by (subst s10; rewrite length_setbn; exact L9).
  assert (Eg1_10 : getbn snum s10 = sn2) by (subst s10 s9; gso; exact Eg1_8).
  set (sn3 := mkBN (bn_d sn2) snb div_n (bn_neg b1) (bn_flags sn2)).
  assert (Hsn3 : bg_ok sn3).
  { unfold bg_ok, bn_dmax. subst sn3. cbn [bn_buf bn_top bn_flags]. rewrite K2. repeat split; try assumption; lia. }
  apply hoare_bind_set; try rewrite L10; try rewrite Eg1_10; try assumption; try reflexivity.
  set (s11 := setbn snum sn3 s10).
  assert (L11 : length (st_bns s11) = length (st_bns s)) by (subst s11; rewrite length_setbn; exact L10).
  assert (Eg1_11 : getbn snum s11 = sn3) by (subst s11; apply getbn_setbn_same; rewrite L10; exact Vsnum).
  assert (Eg3_11 : getbn res s11 = q3) by (subst s11 s10; gso; apply getbn_setbn_same; rewrite L9; exact Vres).
  assert (V0 : 0 < bn_mag b2).
  { pose proof (okv_mag_ge b2 Hb2 Hn2 ltac:(lia)). pose proof (Bp_pos (bn_top b2 - 1)). lia. }
  assert (Hvmag : lval (firstn div_n (bn_buf sd3)) = bn_mag b2 * 2 ^ sh).
  { change (bn_buf sd3) with (bn_buf sd2). rewrite <- Hmag1, <- Emag2. unfold bn_mag. rewrite Etop2, Etop1. reflexivity. }
  rewrite Hvmag in K7, K8.
  destruct (div_values (bn_mag b1) (bn_mag b2) sh (okv_mag_nonneg b1 Hb1) V0 ltac:(lia)) as [DV1 DV2].

  eapply hoare_bind with (R := fun _ s12 => length (st_bns s12) = length (st_bns s) /\ st_ctx s12 = st_ctx s /\ scal_same s s12 /\
       (forall x, rm <> Some x -> getbn x s12 = getbn x s11) /\
       (forall r, rm = Some r -> bn_mag (getbn r s12) = bn_mag b1 mod bn_mag b2 /\ bn_neg (getbn r s12) = bn_neg b1 /\ bn_top (getbn r s12) = div_n)).
  { destruct rm as [r|].
    - destruct (Hrm r eq_refl) as (Vr & Nr & R1' & R2' & R3' & R4' & R5').
      eapply hoare_mono; [apply bn_rshift_fixed_top_spec; try rewrite L11; try assumption; lia|].
      intros [] s12 _ (rm1 & -> & Etrm & Enrm & Emrm). rewrite Eg1_11 in Etrm, Enrm, Emrm.
      rewrite Z.div_small in Etrm, Enrm by lia. cbn [Z.to_nat] in Etrm, Enrm. rewrite Nat.sub_0_r in Etrm.
      split; [rewrite length_setbn; exact L11|]. split; [reflexivity|]. split; [unfold scal_same; repeat split; reflexivity|]. split.
      + intros x Hx. apply getbn_setbn_other. congruence.
      + intros r' Er'. injection Er' as <-. rewrite getbn_setbn_same by (rewrite L11; exact Vr).
        split; [|split; [|exact Etrm]].
        * rewrite Emrm. unfold bn_mag at 1. subst sn3. cbn [bn_buf bn_top]. rewrite K8. exact DV2.
        * rewrite Enrm. subst sn3. cbn [bn_top bn_neg]. destruct (Nat.leb_spec div_n 0); [lia|reflexivity].
    - apply hoare_ret. split; [exact L11|]. split; [reflexivity|]. split; [unfold scal_same; repeat split; reflexivity|].
      split; [intros; reflexivity|]. intros r Er. discriminate. }
  intros [] s12 Hs12 (L12 & Ectx & Escal & Hoth & Hrmv).
  eapply hoare_mono; [apply (BN_CTX_end_spec F s12 fr fp); rewrite Ectx; exact Hfr|].
  intros [] s' Hs' (Ebns & Escal' & Eused & Efr).
  assert (Hget : forall x, getbn x s' = getbn x s12) by (intros x; unfold getbn; rewrite Ebns; reflexivity).
  split; [rewrite Ebns; exact L12|]. split; [eapply scal_same_trans; eassumption|]. split; [exact Eused|]. split; [exact Efr|]. split.
  - intros x X1 X2 X3 X4 X5. rewrite Hget, Hoth by exact X5. subst s11 s10 s9 s8 s7 s5 s3. gso. reflexivity.
  - unfold div_fix_post. cbv zeta. rewrite !Hget.
    assert (Eres : getbn res s12 = q3).
    { destruct rm as [r|]; [|rewrite Hoth by discriminate; exact Eg3_11].
      destruct (Hrm r eq_refl) as (Vr & Nr & R1' & _). rewrite Hoth by congruence. exact Eg3_11. }
    rewrite Eres. split; [|split; [|split]].
    + unfold bn_mag at 1. subst q3 q2. cbn [bn_with_buf bn_buf bn_top]. rewrite K7. exact DV1.
    + reflexivity.
    + subst q3 q2. cbn [bn_with_buf bn_top]. subst loop num_n. lia.
    + intros r Er. rewrite Hget. destruct (Hrmv r Er) as (V1 & V2 & V3). split; [exact V1|]. split; [exact V2|exact V3].
Qed.

Definition div_pre (dv rm : option bnref) (num divisor : bnref) (s : ST) : Prop :=
  live num s /\ live divisor s /\
  (forall d, dv = Some d -> live d s /\ d <> ROne /\ d <> divisor) /\
  (forall r, rm = Some r -> live r s /\ r <> ROne /\ r <> divisor /\ dv <> Some r) /\
  (length (gx_frames (st_ctx s)) < BG_DEPTH)%nat /\ (gx_used (st_ctx s) + 4 <= BG_POOL)%nat /\
  bn_norm (getbn divisor s) /\ (1 <= bn_top (getbn divisor s))%nat /\
  Z.of_nat (bn_top (getbn num s)) + 2 <= BG_DMAX /\ Z.of_nat (bn_top (getbn divisor s)) + 2 <= BG_DMAX.

Definition div_fix_res (dv rm : option bnref) (num0 div0 : BN) (s' : ST) : Prop :=
  (forall d, dv = Some d -> let q := getbn d s' in
     bn_mag q = bn_mag num0 / bn_mag div0 /\ bn_neg q = xorb (bn_neg num0) (bn_neg div0) /\
     Z.of_nat (bn_top q) + Z.of_nat (bn_top div0) = Z.max (Z.of_nat (bn_top num0) + 1) (Z.of_nat (bn_top div0) + 1)) /\
  (forall r, rm = Some r -> let x := getbn r s' in
     bn_mag x = bn_mag num0 mod bn_mag div0 /\ bn_neg x = bn_neg num0 /\ bn_top x = bn_top div0).

Lemma bn_div_fixed_top_spec : forall dv rm num divisor F s,
  div_pre dv rm num divisor s ->
  hoare F s (bn_div_fixed_top ops dv rm num divisor) (fun _ s' =>
     keeps (gx_used (st_ctx s)) (opt_refs dv ++ opt_refs rm) s s' /\
     div_fix_res dv rm (getbn num s) (getbn divisor s) s').
Proof.
  intros dv rm num divisor F s (Lnum & Ldiv & Hdv & Hrm & Hdepth & Hpool & Hn2 & Htop2 & Ht1 & Ht2).
  rewrite bn_div_fixed_top_unfold.
  apply hoare_live.
  { constructor; [exact Lnum|]. constructor; [exact Ldiv|]. apply Forall_app. split.
    - destruct dv as [d|]; cbn [opt_refs]; [|constructor]. constructor; [exact (proj1 (Hdv d eq_refl))|constructor].
    - destruct rm as [r|]; cbn [opt_refs]; [|constructor]. constructor; [exact (proj1 (Hrm r eq_refl))|constructor]. }
  set (u := gx_used (st_ctx s)) in *. unfold live in Lnum, Ldiv. fold u in Lnum, Ldiv.
  eapply hoare_bind; [apply BN_CTX_start_spec; exact Hdepth|].
  intros [] s0 Hs0 (Eb0 & Sc0 & Eu0 & Ef0). fold u in Eu0, Ef0.
  assert (G0 : forall x, getbn x s0 = getbn x s) by (intros x; unfold getbn; rewrite Eb0; reflexivity).

  eapply hoare_bind with (R := fun res s1 => exists k, gx_used (st_ctx s1) = (u + k)%nat /\ (k <= 1)%nat /\
      gx_frames (st_ctx s1) = gx_frames (st_ctx s) ++ [u] /\ scal_same s s1 /\ (length (st_bns s) <= length (st_bns s1))%nat /\
      (forall x, (x < NFIX + u)%nat -> getbn x s1 = getbn x s) /\
      match dv with Some d => res = d /\ k = 0%nat | None => res = RPool u /\ k = 1%nat end).
  { destruct dv as [d|].
    - apply hoare_ret. exists 0%nat. rewrite Nat.add_0_r. split; [exact Eu0|]. split; [lia|]. split; [exact Ef0|].
      split; [exact Sc0|]. split; [rewrite Eb0; lia|]. split; [intros x _; apply G0|]. split; reflexivity.
    - eapply hoare_mono; [apply BN_CTX_get_spec; rewrite Eu0; unfold BG_POOL in *; lia|].
      intros a s1 _ (Ea & Eu1 & Ef1 & Sc1 & Len1 & Oth1 & _). rewrite Eu0 in Ea, Eu1. exists 1%nat.
      split; [lia|]. split; [lia|]. split; [rewrite Ef1; exact Ef0|]. split; [eapply scal_same_trans; eassumption|].
      split; [rewrite <- Eb0; exact Len1|]. split; [|split; [exact Ea|reflexivity]].
      intros x Hx. rewrite Oth1 by (rewrite Ea; unfold RPool; lia). apply G0. }
  intros res s1 Hs1 (k & Eu1 & Hk & Ef1 & Sc1 & Len1 & Oth1 & Hres).

  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu1; unfold BG_POOL in *; lia|].
  intros tmp s2 Hs2 (Ea2 & Eu2 & Ef2 & Sc2 & Len2 & Oth2 & _). rewrite Eu1 in Ea2, Eu2.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu2; unfold BG_POOL in *; lia|].
  intros snum s3 Hs3 (Ea3 & Eu3 & Ef3 & Sc3 & Len3 & Oth3 & _). rewrite Eu2 in Ea3, Eu3.
  eapply hoare_bind; [apply BN_CTX_get_spec; rewrite Eu3; unfold BG_POOL in *; lia|].
  intros sdiv s4 Hs4 (Ea4 & Eu4 & Ef4 & Sc4 & Len4 & Oth4 & _). rewrite Eu3 in Ea4, Eu4.

  assert (G4 : forall x, (x < NFIX + u)%nat -> getbn x s4 = getbn x s).
  { intros x Hx. rewrite Oth4, Oth3, Oth2 by (subst; unfold RPool; lia). apply Oth1. exact Hx. }
  assert (Hvalid : forall x, (x < NFIX + S (S (S (u + k))))%nat -> (x < length (st_bns s4))%nat).
  { intros x Hx. apply live_valid; [exact Hs4|]. unfold live. rewrite Eu4. exact Hx. }
  assert (Eres : (res < NFIX + u)%nat /\ res <> ROne /\ res <> divisor /\ dv = Some res \/ res = RPool u /\ k = 1%nat /\ dv = None).
  { destruct dv as [d|]; destruct Hres as [-> ->]; [left|right; auto].
    destruct (Hdv d eq_refl) as (A1 & A2 & A3). unfold live in A1. fold u in A1. auto. }
  assert (Hrm' : forall r, rm = Some r -> (r < NFIX + u)%nat /\ r <> ROne /\ r <> divisor /\ r <> res).
  { intros r Er. destruct (Hrm r Er) as (A1 & A2 & A3 & A4). unfold live in A1. fold u in A1. repeat split; try assumption.
    destruct Eres as [(_ & _ & _ & E)|(E & _ & _)]; [congruence|rewrite E; unfold RPool; lia]. }
  subst tmp snum sdiv.
  assert (Hres_lt : (res < NFIX + S (S (S (u + k))))%nat).
  { destruct Eres as [(E & _)|(E & E' & _)]; [lia|rewrite E, E'; unfold RPool; lia]. }
  assert (Hres_tmp : forall j, ndiff res (RPool (j + (u + k)))).
  { intros j. destruct Eres as [(E & _)|(E & E' & _)]; [|rewrite E, E']; unfold ndiff, RPool; lia. }
  eapply hoare_mono.
  { apply (div_core_spec res (RPool (u + k)) (RPool (S (u + k))) (RPool (S (S (u + k)))) rm num divisor (gx_frames (st_ctx s)) u).
    - apply Hvalid. exact Hres_lt.
    - apply Hvalid. unfold RPool. lia.
    - apply Hvalid. unfold RPool. lia.
    - apply Hvalid. unfold RPool. lia.
    - apply Hvalid. lia.
    - apply Hvalid. lia.
    - destruct Eres as [(_ & E & _)|(E & _)]; [exact E|rewrite E; unfold ndiff, RPool, NFIX, ROne; lia].
    - unfold ndiff, RPool, NFIX, ROne. lia.
    - unfold ndiff, RPool, NFIX, ROne. lia.
    - unfold ndiff, RPool, NFIX, ROne. lia.
    - intros r Er. destruct (Hrm' r Er) as (A1 & A2 & A3 & A4).
      split; [apply Hvalid; lia|]. unfold ndiff, RPool. repeat split; try assumption; lia.
    - unfold ndiff, RPool. lia.
    - unfold ndiff, RPool. lia.
    - unfold ndiff, RPool. lia.
    - apply (Hres_tmp 0%nat).
    - apply (Hres_tmp 1%nat).
    - apply (Hres_tmp 2%nat).
    - destruct Eres as [(_ & _ & E & _)|(E & _)]; [exact E|rewrite E; unfold ndiff, RPool; lia].
    - unfold ndiff, RPool. lia.
    - unfold ndiff, RPool. lia.
    - unfold ndiff, RPool. lia.
    - unfold ndiff, RPool. lia.
    - unfold ndiff, RPool. lia.
    - unfold ndiff, RPool. lia.
    - rewrite Ef4, Ef3, Ef2. exact Ef1.
    - rewrite G4 by lia. exact Hn2.
    - rewrite G4 by lia. exact Htop2.
    - rewrite G4 by lia. exact Ht1.
    - rewrite G4 by lia. exact Ht2. }
  intros [] s' Hs' (Len' & Sc' & Eu' & Ef' & Oth' & Hpost). rewrite !G4 in Hpost by lia.
  split.
  - split; [split|].
    + unfold ctx_keep. split; [lia|]. split; assumption.
    + intros x Hx Hnin. rewrite Oth'; [apply G4; exact Hx| | | | |].
      * destruct Eres as [(_ & _ & _ & E)|(E & _)]; [|rewrite E; unfold ndiff, RPool; lia].
        intros ->. apply Hnin. rewrite E. cbn [opt_refs app]. left. reflexivity.
      * unfold ndiff, RPool. lia.
      * unfold ndiff, RPool. lia.
      * unfold ndiff, RPool. lia.
      * intros E. apply Hnin. rewrite E. apply in_or_app. right. left. reflexivity.
    + eapply scal_same_trans; [|exact Sc']. eapply scal_same_trans; [|exact Sc4]. eapply scal_same_trans; [|exact Sc3].
      eapply scal_same_trans; [|exact Sc2]. exact Sc1.
  - destruct Hpost as (P1 & P2 & P3 & P4). split.
    + intros d Ed. destruct Eres as [(_ & _ & _ & E)|(_ & _ & E)]; [|congruence]. assert (d = res) by congruence. subst d. auto.
    + exact P4.
Qed.

Definition div_res (dv rm : option bnref) (num0 div0 : BN) (s' : ST) : Prop :=
  (forall d, dv = Some d -> let q := getbn d s' in
     bn_canon q /\ bn_mag q = bn_mag num0 / bn_mag div0 /\
     bn_neg q = (xorb (bn_neg num0) (bn_neg div0) && negb (bn_top q =? 0)%nat) /\
     Z.of_nat (bn_top q) + Z.of_nat (bn_top div0) <= Z.max (Z.of_nat (bn_top num0) + 1) (Z.of_nat (bn_top div0) + 1)) /\
  (forall r, rm = Some r -> let x := getbn r s' in
     bn_canon x /\ bn_mag x = bn_mag num0 mod bn_mag div0 /\
     bn_neg x = (bn_neg num0 && negb (bn_top x =? 0)%nat) /\ (bn_top x <= bn_top div0)%nat).

Lemma opt_correct_top_spec : forall (o : option bnref) F s,
  (forall r, o = Some r -> (r < length (st_bns s))%nat /\ r <> ROne) ->
  hoare F s (match o with Some r => bbind ops (bget ops r) (fun b => bset ops r (bn_correct_top_pure b)) | None => bret ops tt end)
        (fun _ s' => match o with Some r => s' = setbn r (bn_correct_top_pure (getbn r s)) s | None => s' = s end).
Proof.
  intros [r|] F s H.
  - destruct (H r eq_refl) as [Hr Hn]. eapply hoare_mono; [apply correct_top_spec; assumption|].
    intros [] s' _ (b' & -> & ->). reflexivity.
  - apply hoare_ret. reflexivity.
Qed.

Lemma BN_div_spec : forall dv rm num divisor F s,
  div_pre dv rm num divisor s ->
  hoare F s (BN_div ops dv rm num divisor) (fun _ s' =>
     keeps (gx_used (st_ctx s)) (opt_refs dv ++ opt_refs rm) s s' /\
     div_res dv rm (getbn num s) (getbn divisor s) s').
Proof.
  intros dv rm num divisor F s Hpre. pose proof Hpre as (Lnum & Ldiv & Hdv & Hrm & Hdepth & Hpool & Hn2 & Htop2 & Ht1 & Ht2).
  apply hoare_wf. intros Hs. unfold BN_div. apply hoare_bind_get.
  destruct (Nat.eqb_spec (bn_top (getbn divisor s)) 0) as [|_]; [lia|].
  destruct Hn2 as [Hz|Hnz]; [lia|].
  destruct (Z.eqb_spec (nth (bn_top (getbn divisor s) - 1) (bn_buf (getbn divisor s)) 0) 0) as [E|_]; [contradiction|].
  set (u := gx_used (st_ctx s)) in *. set (num0 := getbn num s) in *. set (div0 := getbn divisor s) in *.
  eapply hoare_bind; [apply bn_div_fixed_top_spec; exact Hpre|].
  intros [] s1 Hs1 (K1 & Q1 & R1). fold u num0 div0 in K1, Q1, R1.
  assert (Hval1 : forall r, live r s -> (r < length (st_bns s1))%nat).
  { intros r Hr. apply live_valid; [exact Hs1|]. eapply keeps_live; eassumption. }
  eapply hoare_bind; [apply opt_correct_top_spec|].
  { intros r Er. destruct (Hdv r Er) as (A1 & A2 & A3). split; [apply Hval1; exact A1|exact A2]. }
  intros [] s2 Hs2 E2.
  assert (K2 : keeps u (opt_refs dv ++ opt_refs rm) s s2 /\ (forall r, rm = Some r -> getbn r s2 = getbn r s1) /\ length (st_bns s2) = length (st_bns s1)).
  { destruct dv as [d|]; [|subst s2; split; [exact K1|split; [intros; reflexivity|reflexivity]]]. subst s2. split; [|split].
    - eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K1|apply keeps_setbn]].
      intros r Hin _. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]]; [exact Hin|]. cbn [opt_refs app]. left. reflexivity.
    - intros r Er. destruct (Hrm r Er) as (_ & _ & _ & A4). apply getbn_setbn_other. congruence.
    - apply length_setbn. }
  destruct K2 as (K2 & Hrm2 & Len2).
  eapply hoare_mono; [apply opt_correct_top_spec|].
  { intros r Er. destruct (Hrm r Er) as (A1 & A2 & A3 & A4). split; [rewrite Len2; apply Hval1; exact A1|exact A2]. }
  intros [] s3 Hs3 E3. split.
  - destruct rm as [r|]; [|subst s3; exact K2]. subst s3.
    eapply keeps_weaken; [apply Nat.le_refl| |eapply keeps_trans; [exact K2|apply keeps_setbn]].
    intros r' Hin _. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]]; [exact Hin|]. apply in_or_app. right. left. reflexivity.
  - split.
    + intros d Ed. cbv zeta.
      assert (Hd1 : (d < length (st_bns s1))%nat) by (destruct (Hdv d Ed) as (A1 & _); apply Hval1; exact A1).
      assert (Hdn : d <> ROne) by (destruct (Hdv d Ed) as (_ & A2 & _); exact A2).
      assert (Eg : getbn d s3 = bn_correct_top_pure (getbn d s1)).
      { rewrite Ed in E2. subst s2. destruct rm as [r|].
        - subst s3. destruct (Hrm r eq_refl) as (_ & _ & _ & A4). rewrite getbn_setbn_other by congruence.
          apply getbn_setbn_same. exact Hd1.
        - subst s3. apply getbn_setbn_same. exact Hd1. }
      rewrite Eg. destruct (bg_correct_top_ok (getbn d s1) (st_wf_ok d s1 Hs1 Hd1 Hdn)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      destruct (Q1 d Ed) as (M1 & M2 & M3). split; [exact C2|]. split; [rewrite C3; exact M1|]. split; [rewrite C7, M2; reflexivity|lia].
    + intros r Er. cbv zeta.
      assert (Hr1 : (r < length (st_bns s1))%nat) by (destruct (Hrm r Er) as (A1 & _); apply Hval1; exact A1).
      assert (Hrn : r <> ROne) by (destruct (Hrm r Er) as (_ & A2 & _); exact A2).
      rewrite Er in E3. subst s3. rewrite getbn_setbn_same by (rewrite Len2; exact Hr1). rewrite (Hrm2 r Er).
      destruct (bg_correct_top_ok (getbn r s1) (st_wf_ok r s1 Hs1 Hr1 Hrn)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      destruct (R1 r Er) as (M1 & M2 & M3). split; [exact C2|]. split; [rewrite C3; exact M1|]. split; [rewrite C7, M2; reflexivity|lia].
Qed.

End DivSpec.
