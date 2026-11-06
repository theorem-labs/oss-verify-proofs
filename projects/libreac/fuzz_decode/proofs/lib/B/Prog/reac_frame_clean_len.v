From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_frame_clean_len_c.
Import ListNotations.
Open Scope Z_scope.

Lemma lor_low : forall k x y, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (y * 2^k) = y * 2^k + x.
Proof.
  intros k x y Hk Hx Hy. rewrite <- Z.shiftl_mul_pow2 by lia.
  assert (H0 : Z.land x (Z.shiftl y k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k).
    - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite <- (Z.mod_small x (2^k)) by lia.
      rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- (Z.lxor_lor _ _ H0), <- (Z.add_nocarry_lxor _ _ H0), Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma rot_split : forall y, 0 <= y < 2^64 ->
  Z.lor (Z.shiftr y 2) ((Z.shiftl y 62) mod 2^64) = (y mod 4) * 2^62 + y / 4.
Proof.
  intros y Hy.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftl_mul_pow2 by lia.
  replace (2^64) with (4 * 2^62) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia.
  change (2^2) with 4.
  apply lor_low; [lia | split | apply Z.mod_pos_bound; lia].
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma rot_wrap : forall Y,
  (Z.lor ((Z.shiftr (Y mod 2^64) 2) mod 2^64) ((Z.shiftl (Y mod 2^64) 62) mod 2^64)) mod 2^64 =
  ((Y mod 2^64) mod 4) * 2^62 + (Y mod 2^64) / 4.
Proof.
  intros Y.
  assert (Hy : 0 <= Y mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
  set (y := Y mod 2^64) in *. clearbody y.
  rewrite (Z.mod_small (Z.shiftr y 2)).
  2: { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (rot_split y Hy). apply Z.mod_small.
  assert (0 <= y mod 4 < 4) by (apply Z.mod_pos_bound; lia).
  assert (0 <= y / 4 < 2^62) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  lia.
Qed.

Lemma c2_core : forall x y, 0 <= x < 2^64 -> y = (x * KM) mod 2^64 ->
  ((y mod 4) * 2^62 + y / 4 < KT <-> x mod 36 = 0).
Proof.
  intros x y Hx Hy. unfold KM, KT in *.
  set (s := (x * 10248191152060862009) / 2^64) in *.
  assert (Es : x * 10248191152060862009 = 2^64 * s + y) by (subst y s; apply Z.div_mod; lia).
  assert (Ry : 0 <= y < 2^64) by (subst y; apply Z.mod_pos_bound; lia).
  clearbody s. clear Hy.
  set (b := y mod 4). set (a := y / 4).
  assert (Ea : y = 4 * a + b) by (apply Z.div_mod; lia).
  assert (Rb : 0 <= b < 4) by (apply Z.mod_pos_bound; lia).
  set (f := x mod 36). set (e := x / 36).
  assert (Ex : x = 36 * e + f) by (apply Z.div_mod; lia).
  assert (Rf : 0 <= f < 36) by (apply Z.mod_pos_bound; lia).
  clearbody a b e f.
  change (2^64) with 18446744073709551616 in *.
  change (2^62) with 4611686018427387904 in *.
  split.
  - intro Hlt.
    assert (Hb : b = 0) by lia. subst b.
    remember (9 * s - 5 * x) as t eqn:Et.
    assert (E9 : x = 36 * a + 18446744073709551616 * t) by lia.
    assert (Ht : t = 0 \/ t = -1) by lia.
    destruct Ht as [Ht | Ht]; subst t; lia.
  - intro Hf. subst f.
    remember (20 * e - s) as t eqn:Et.
    assert (E4 : y = 4 * e + 18446744073709551616 * t) by lia.
    assert (Ht : t = 0) by lia. subst t.
    lia.
Qed.

Lemma c2 : forall n, 54 <= n < 2^64 ->
  (((n * KM + -6) mod 2^64) mod 4 * 2^62 + ((n * KM + -6) mod 2^64) / 4 < KT <-> (n - 52) mod 36 = 2).
Proof.
  intros n Hn.
  assert (Ey : (n * KM + -6) mod 2^64 = ((n - 54) * KM) mod 2^64).
  { replace (n * KM + -6) with ((n - 54) * KM + 30 * 2^64) by (unfold KM; lia).
    apply Z.mod_add. lia. }
  rewrite Ey. rewrite (c2_core (n - 54) _ ltac:(lia) eq_refl).
  replace (n - 52) with ((n - 54) + 2) by lia.
  set (x := n - 54).
  assert (Ex : x = 36 * (x / 36) + x mod 36) by (apply Z.div_mod; lia).
  assert (Rf : 0 <= x mod 36 < 36) by (apply Z.mod_pos_bound; lia).
  assert (Ex2 : x + 2 = 36 * ((x + 2) / 36) + (x + 2) mod 36) by (apply Z.div_mod; lia).
  assert (Rf2 : 0 <= (x + 2) mod 36 < 36) by (apply Z.mod_pos_bound; lia).
  lia.
Qed.

Theorem reac_frame_clean_len_holds : reac_frame_clean_len_contract.
Proof.
  unfold reac_frame_clean_len_contract, REAC_FRAME_CLEAN_LEN, A_M, A_T.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HM HT.
  assert (RM : ov_read_bytes rsegs m (wa 0x10310) 8 = Some (le8 (Z_to_bv 64 KM))).
  { replace (wa 0x10310) with (wa (0x10310 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x10310 _ 0 8 HM ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  assert (RT : ov_read_bytes rsegs m (wa 0x103c8) 8 = Some (le8 (Z_to_bv 64 KT))).
  { replace (wa 0x103c8) with (wa (0x103c8 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x103c8 _ 0 8 HT ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  step. step.
  if_cases HC.
  - step.
    replace (Z_to_bv 64 (reac_frame_clean_len_model (bv_unsigned a0))) with a0.
    + apply evt_done. do 3 eexists. reflexivity.
    + unfold bv_ltu in HC. rewrite (unsigned_lit 54) in HC by lia. apply Z.ltb_lt in HC.
      unfold reac_frame_clean_len_model. rewrite (proj2 (Z.leb_gt 54 (bv_unsigned a0)) HC). cbn [andb].
      symmetry. apply Z_to_bv_lit_self.
  - assert (Hn : 54 <= bv_unsigned a0 < 2^64).
    { unfold bv_ltu in HC. rewrite (unsigned_lit 54) in HC by lia. apply Z.ltb_ge in HC.
      pose proof (bv_unsigned_in_range 64 a0) as Hr. unfold bv_modulus in Hr. lia. }
    step. step. step. step. step. step. step. step. step. step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (bv_unsigned a0 + ?E)] =>
      replace (Z_to_bv 64 (bv_unsigned a0 + E)) with (Z_to_bv 64 (reac_frame_clean_len_model (bv_unsigned a0))) end.
    + apply evt_done. do 3 eexists. reflexivity.
    + rewrite v_sltu_b2z. rewrite (unsigned_lit KM) by (unfold KM; lia).
      rewrite !unsigned_lit_wrap. rewrite rot_wrap. rewrite (Z.mod_small KT) by (unfold KT; lia).
      set (n := bv_unsigned a0) in *. clearbody n.
      destruct (c2 n Hn) as [C1 C2].
      unfold reac_frame_clean_len_model. rewrite (proj2 (Z.leb_le 54 n)) by lia. cbn [andb].
      match goal with |- context [Z.ltb ?A ?B] => destruct (Z.ltb_spec A B) as [L | L] end;
        cbn [Z.b2z];
        match goal with |- context [Z.land ?X 18446744073709551614] =>
          let v := eval vm_compute in (Z.land X 18446744073709551614) in change (Z.land X 18446744073709551614) with v end.
      * rewrite (proj2 (Z.eqb_eq _ 2) (C1 L)). cbv iota.
        apply bv_eq. rewrite !unsigned_lit_wrap.
        replace (n + 18446744073709551614) with ((n - 2) + 1 * 2^64) by lia.
        rewrite Z.mod_add by lia. reflexivity.
      * assert (N : (n - 52) mod 36 <> 2) by (intro E; specialize (C2 E); lia).
        rewrite (proj2 (Z.eqb_neq _ 2) N). cbv iota. f_equal. lia.
Qed.
