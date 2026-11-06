(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma srli_W : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k -> v_srli (W x) k = W (x / 2 ^ k).
Proof. intros x k Hx Hk. unfold v_srli. rewrite Wu by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma srli3_W : forall x, 0 <= x < 2 ^ 64 -> v_srli (W x) 3 = W (x / 8).
Proof. intros x Hx. rewrite srli_W by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_high_mask : forall u k, 0 <= u < 2 ^ 64 -> 0 <= k <= 64 ->
  Z.land u (2 ^ 64 - 2 ^ k) = u / 2 ^ k * 2 ^ k.
Proof.
  intros u k Hu Hk.
  replace (u / 2 ^ k * 2 ^ k) with (Z.shiftl (Z.shiftr u k) k)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec.
  destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
  - f_equal.
    replace (2 ^ 64 - 2 ^ k) with (Z.shiftl (Z.ones (64 - k)) k).
    2:{ rewrite Z.shiftl_mul_pow2, Z.ones_equiv by lia.
        replace (2 ^ 64) with (2 ^ (64 - k) * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). lia. }
    rewrite Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases i k) as [Hik|Hik].
    + rewrite Z.testbit_neg_r by lia. rewrite Z.ones_spec_low by lia. reflexivity.
    + rewrite Z.ones_spec_low by lia. rewrite Z.ones_spec_high by lia. reflexivity.
  - assert (Hz : Z.testbit u i = false).
    { destruct (Z.eq_dec u 0) as [->|Hnz]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [|lia].
      apply Z.log2_lt_pow2; lia. }
    rewrite Hz. reflexivity.
Qed.

Lemma andi_m8_W : forall x, 0 <= x < 2 ^ 64 -> v_andi (W x) (-8) = W (x / 8 * 8).
Proof.
  intros x Hx. unfold v_andi. rewrite Wu by lia.
  change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3). rewrite land_high_mask by lia. reflexivity.
Qed.

Lemma andi7_W : forall x, 0 <= x < 2 ^ 64 -> v_andi (W x) 7 = W (x mod 8).
Proof.
  intros x Hx. rewrite <- (W_u (v_andi (W x) 7)). f_equal. change 7 with (Z.ones 3).
  rewrite u_andi_ones by lia. rewrite Wu by lia. reflexivity.
Qed.

Lemma Wu_neg : forall z, - 2 ^ 64 < z < 0 -> bv_unsigned (W z) = z + 2 ^ 64.
Proof.
  intros z Hz. rewrite Wu_mod. symmetry. apply Z.mod_unique with (-1); lia.
Qed.

(* [comment removed for export] *)
Lemma poisoned_zero : forall u m, 0 <= m <= 7 -> (u = 0 \/ m < u <= 7) ->
  v_and (v_sltu (W 0) (W u)) (v_xori (v_slt (W m) (W u)) 1) = W 0.
Proof.
  intros u m Hm [->|Hu].
  - apply bv_eq. rewrite u_and. change (bv_unsigned (v_sltu (W 0) (W 0))) with 0. rewrite Z.land_0_l. reflexivity.
  - assert (E : v_slt (W m) (W u) = W 1).
    { unfold v_slt, c_lts, bv_lts. rewrite !Ws by lia. destruct (Z.ltb_spec m u); [reflexivity | lia]. }
    rewrite E. apply bv_eq. rewrite u_and.
    change (bv_unsigned (v_xori (W 1) 1)) with 0. rewrite Z.land_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u_not_W : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (v_xori (W x) (-1)) = 2 ^ 64 - 1 - x.
Proof.
  intros x Hx. unfold v_xori. rewrite (Wu x) by lia. change (bv_wrap 64 (-1)) with (Z.ones 64).
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
    - rewrite Z.ones_spec_low by lia. rewrite andb_true_r. apply xorb_true_r.
    - rewrite Z.ones_spec_high by lia. rewrite andb_false_r, xorb_false_r.
      destruct (Z.eq_dec x 0) as [->|Hnz]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite E, Z.land_ones by lia. unfold Z.lnot.
  assert (Em : (Z.pred (- x)) mod 2 ^ 64 = 2 ^ 64 - 1 - x) by (symmetry; apply Z.mod_unique with (-1); unfold Z.pred; lia).
  rewrite Em. apply Wu. lia.
Qed.

(* [comment removed for export] *)
Lemma align_dn_le : forall x, x / 8 * 8 <= x < x / 8 * 8 + 8.
Proof. intros x. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

Lemma align_dn_mod : forall x, (x / 8 * 8) mod 8 = 0.
Proof. intros x. apply Z.mod_mul. lia. Qed.

Lemma align_up_le : forall x, x <= (x + 7) / 8 * 8 < x + 8.
Proof. intros x. pose proof (align_dn_le (x + 7)). lia. Qed.

Lemma aligned_step : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> a < b -> a + 8 <= b.
Proof.
  intros a b Ha Hb Hlt. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod b 8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma lb_small : forall u, 0 <= u <= 127 -> v_lb (Z_to_bv 8 (bv_unsigned (W u))) = W u.
Proof.
  intros u Hu. rewrite Wu by lia. unfold v_lb. f_equal.
  unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  rewrite (Z.mod_small u) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SB : Z := 0x7fff8000.
Definition sha (x : Z) : Z := x / 8 + SB.

(* [comment removed for export] *)
Definition LOMEM_END : Z := 0x7fff8000.          (* [comment removed for export] *)
Definition HIMEM_BEG : Z := 0x10007fff8000.      (* [comment removed for export] *)
Definition HIMEM_END : Z := 0x800000000000.      (* [comment removed for export] *)

Definition inmem (x : Z) : Prop := 0 <= x < LOMEM_END \/ HIMEM_BEG <= x < HIMEM_END.

(* [comment removed for export] *)
Definition memrange (a n : Z) : Prop :=
  0 <= n /\ ((0 <= a /\ a + n + 8 <= LOMEM_END) \/ (HIMEM_BEG <= a /\ a + n + 8 <= HIMEM_END)).

Lemma memrange_inmem : forall a n x, memrange a n -> a <= x <= a + n + 7 -> inmem x.
Proof. intros a n x [Hn H] Hx. unfold inmem. lia. Qed.

(* [comment removed for export] *)
Lemma sha_range : forall x, 0 <= x < HIMEM_END -> SB <= sha x < HIMEM_BEG.
Proof.
  intros x Hx. unfold sha, SB, HIMEM_BEG, HIMEM_END in *.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  assert (x / 8 < 0x100000000000) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma sha_mono : forall x y, x <= y -> sha x <= sha y.
Proof. intros x y H. unfold sha. pose proof (Z.div_le_mono x y 8 ltac:(lia) H). lia. Qed.

Lemma sha_add8 : forall g i, sha (g + 8 * i) = sha g + i.
Proof. intros g i. unfold sha. replace (g + 8 * i) with (g + i * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma sha_addr_l : forall x, 0 <= x < 2 ^ 64 -> v_add (W SB) (v_srli (W x) 3) = W (sha x).
Proof. intros x Hx. rewrite srli3_W by lia. rewrite add_W. f_equal. unfold sha. lia. Qed.

Lemma sha_addr_r : forall x, 0 <= x < 2 ^ 64 -> v_add (v_srli (W x) 3) (W SB) = W (sha x).
Proof. intros x Hx. rewrite srli3_W by lia. rewrite add_W. reflexivity. Qed.

Section Shadow.
Variable SEGS : list Segment.

Definition acc1 (M : mem) (x : Z) : Prop :=
  exists s : byte, M (W (sha x)) = Some s /\ (bv_unsigned s = 0 \/ (x mod 8 < bv_unsigned s <= 7)).

Definition addr_ok (M : mem) (a n : Z) : Prop := forall x, a <= x < a + n -> acc1 M x.

Definition zeros (M : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> M (W (a + i)) = Some (Z_to_bv 8 0).

Lemma addr_ok_sub : forall M a n a' n', addr_ok M a n -> a <= a' -> a' + n' <= a + n -> addr_ok M a' n'.
Proof. intros M a n a' n' H H1 H2 x Hx. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma acc1_unch : forall M0 M (P : word -> Prop) x,
  unch M0 M P -> 0 <= x < HIMEM_END -> (forall y, P y -> ~ (SB <= bv_unsigned y < HIMEM_BEG)) ->
  acc1 M0 x -> acc1 M x.
Proof.
  intros M0 M P x HU Hx HP (s & Hs & Hc). exists s. split; [|exact Hc].
  rewrite HU; [exact Hs|]. intros HPy. apply (HP _ HPy).
  pose proof (sha_range x Hx) as Hr. unfold SB, HIMEM_BEG in *. rewrite Wu by lia. exact Hr.
Qed.

Lemma addr_ok_unch : forall M0 M (P : word -> Prop) a n,
  unch M0 M P -> 0 <= a -> a + n <= HIMEM_END -> (forall y, P y -> ~ (SB <= bv_unsigned y < HIMEM_BEG)) ->
  addr_ok M0 a n -> addr_ok M a n.
Proof. intros M0 M P a n HU Ha Hn HP H x Hx. eapply acc1_unch; [exact HU | lia | exact HP | apply H, Hx]. Qed.

(* [comment removed for export] *)
Lemma sh_load : forall M x, acc1 M x -> 0 <= x < HIMEM_END ->
  exists u, load_ok SEGS M (W (sha x)) 1 (W u) /\ (u = 0 \/ x mod 8 < u <= 7).
Proof.
  intros M x (s & Hs & Hc) Hx. exists (bv_unsigned s). split; [|exact Hc].
  exists [s]. split.
  - cbn [rdn]. rewrite Hs. reflexivity.
  - rewrite bytes_le_1. pose proof (bv_unsigned_in_range 8 s) as Hb. change (bv_modulus 8) with 256 in Hb.
    rewrite Wu by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma acc1_full_zero : forall M g, g mod 8 = 0 -> addr_ok M g 8 -> M (W (sha g)) = Some (Z_to_bv 8 0).
Proof.
  intros M g Hg H. destruct (H (g + 7) ltac:(lia)) as (s & Hs & Hc).
  assert (E : sha (g + 7) = sha g).
  { unfold sha. f_equal. pose proof (Z.div_mod g 8 ltac:(lia)) as Hd. rewrite Hg in Hd.
    replace (g + 7) with (7 + g / 8 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  rewrite E in Hs. rewrite Hs. f_equal.
  assert (Hm : (g + 7) mod 8 = 7).
  { pose proof (Z.div_mod g 8 ltac:(lia)) as Hd. rewrite Hg in Hd.
    replace (g + 7) with (7 + g / 8 * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  rewrite Hm in Hc. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0. lia.
Qed.

(* [comment removed for export] *)
Lemma addr_ok_zeros : forall M a n, addr_ok M a n -> 0 <= a ->
  zeros M (sha ((a + 7) / 8 * 8)) ((a + n) / 8 - (a + 7) / 8).
Proof.
  intros M a n H Ha i Hi.
  rewrite <- sha_add8.
  apply acc1_full_zero.
  - replace ((a + 7) / 8 * 8 + 8 * i) with (((a + 7) / 8 + i) * 8) by lia. apply Z.mod_mul. lia.
  - eapply addr_ok_sub; [exact H | |].
    + pose proof (align_up_le a). lia.
    + pose proof (align_dn_le (a + n)). lia.
Qed.

(* [comment removed for export] *)
Lemma addr_ok_inner_zero : forall M a n x, addr_ok M a n -> 0 <= a -> a <= x -> sha x < sha (a + n - 1) ->
  M (W (sha x)) = Some (Z_to_bv 8 0).
Proof.
  intros M a n x H Ha Hx Hs.
  assert (Hg : x / 8 < (a + n - 1) / 8) by (unfold sha in Hs; lia).
  pose proof (align_dn_le x) as Hx8. pose proof (align_dn_le (a + n - 1)) as He8.
  assert (Hle : x / 8 * 8 + 8 <= (a + n - 1) / 8 * 8) by lia.
  replace (sha x) with (sha (x / 8 * 8)) by (unfold sha; rewrite Z.div_mul by lia; reflexivity).
  destruct (H (x / 8 * 8 + 7) ltac:(lia)) as (s & Hs' & Hc).
  assert (E : sha (x / 8 * 8 + 7) = sha (x / 8 * 8)).
  { unfold sha. f_equal. replace (x / 8 * 8 + 7) with (7 + x / 8 * 8) by lia. rewrite Z.div_add by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite E in Hs'. rewrite Hs'. f_equal.
  assert (Hm : (x / 8 * 8 + 7) mod 8 = 7).
  { replace (x / 8 * 8 + 7) with (7 + x / 8 * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  rewrite Hm in Hc. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0. lia.
Qed.

Lemma addr_ok_scan_zeros : forall M a n, addr_ok M a n -> 0 <= a -> 0 < n ->
  zeros M (sha a) (sha (a + n - 1) - sha a).
Proof.
  intros M a n H Ha Hn i Hi.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite Z.add_0_r. apply (addr_ok_inner_zero M a n a H Ha); lia.
  - assert (E : sha a + i = sha (a / 8 * 8 + 8 * i)).
    { rewrite sha_add8. unfold sha. rewrite Z.div_mul by lia. reflexivity. }
    rewrite E. pose proof (align_dn_le a).
    apply (addr_ok_inner_zero M a n _ H Ha); [lia | rewrite <- E; lia].
Qed.

(* [comment removed for export] *)
Definition shw_ok (M : mem) (a n : Z) : Prop :=
  rd_ok M (sha a / 8 * 8) (sha (a + n - 1) / 8 * 8 + 8 - sha a / 8 * 8).

Lemma shw_ok_sub : forall M a n a' n', shw_ok M a n -> a <= a' -> 0 < n' -> a' + n' <= a + n -> shw_ok M a' n'.
Proof.
  intros M a n a' n' H H1 Hn' H2. unfold shw_ok in *.
  pose proof (sha_mono a a' H1). pose proof (sha_mono (a' + n' - 1) (a + n - 1) ltac:(lia)).
  pose proof (Z.div_le_mono (sha a) (sha a') 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (sha (a' + n' - 1)) (sha (a + n - 1)) 8 ltac:(lia) ltac:(lia)).
  eapply rd_ok_sub; [exact H | lia | lia].
Qed.

Lemma zeros_sub : forall M a n a' n', zeros M a n -> a <= a' -> a' + n' <= a + n -> zeros M a' n'.
Proof.
  intros M a n a' n' H H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma zeros_rd_ok : forall M a n, zeros M a n -> rd_ok M a n.
Proof. intros M a n H i Hi. rewrite (H i Hi). discriminate. Qed.

Lemma zeros_grows_unch : forall M0 M (P : word -> Prop) a n,
  unch M0 M P -> 0 <= a -> a + n < 2 ^ 64 -> (forall x, inr x a n -> ~ P x) -> zeros M0 a n -> zeros M a n.
Proof.
  intros M0 M P a n HU Ha Hn HP H i Hi. rewrite HU; [apply H, Hi|]. apply HP. unfold inr. rewrite Wu by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma load1_zeros : forall M a n x, zeros M a n -> a <= x < a + n ->
  load_ok SEGS M (W x) 1 (W 0).
Proof.
  intros M a n x H Hx. exists [Z_to_bv 8 0]. split; [|reflexivity].
  cbn [rdn]. replace x with (a + (x - a)) by lia. rewrite (H (x - a)) by lia. reflexivity.
Qed.

Lemma W_succ' : forall a, (W a + 1)%bv = W (a + 1).
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1.
  rewrite !Wu_mod. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma rdn_zeros : forall M a n (k : nat) x, zeros M a n -> a <= x -> x + Z.of_nat k <= a + n ->
  rdn SEGS M (W x) k = Some (repeat (Z_to_bv 8 0) k).
Proof.
  intros M a n k. induction k as [|k IH]; intros x H Hx Hk; [reflexivity|].
  cbn [rdn repeat]. replace x with (a + (x - a)) at 1 by lia. rewrite (H (x - a)) by lia.
  rewrite W_succ'. rewrite IH by (try assumption; lia). reflexivity.
Qed.

Lemma load8_zeros : forall M a n x, zeros M a n -> a <= x -> x + 8 <= a + n ->
  load_ok SEGS M (W x) 8 (W 0).
Proof.
  intros M a n x H Hx Hk. exists (repeat (Z_to_bv 8 0) 8). split; [|reflexivity].
  apply (rdn_zeros M a n 8 x H Hx). lia.
Qed.

End Shadow.
