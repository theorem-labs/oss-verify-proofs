From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import reac_upstream_channels_c.
Import ListNotations.
Open Scope Z_scope.

Lemma upstream_small : forall len, 0 <= len < 124 -> upstream_result len = -1.
Proof.
  intros len H. unfold upstream_result, upstream_ok.
  destruct (Z.leb_spec 52 len) as [H52|H52]; [|reflexivity].
  assert (D : (2 <=? upstream_width len) = false).
  { apply Z.leb_gt. unfold upstream_width.
    assert (Q : 0 <= (len - 52) / 36 < 2) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    rewrite Z.mod_small by lia. lia. }
  rewrite D, andb_false_r. reflexivity.
Qed.

Lemma div36_magic : forall x, 0 <= x < 2^64 ->
  Z.shiftr (Z.shiftr (x * 16397105843297379215) 64) 5 = x / 36.
Proof.
  intros x Hx.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  change (2 ^ 64 * 2 ^ 5) with 590295810358705651712.
  assert (Hq : 0 <= x / 36 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (Hr : 0 <= x mod 36 < 36) by (apply Z.mod_pos_bound; lia).
  assert (Hd : x = 36 * (x / 36) + x mod 36) by (apply Z.div_mod; lia).
  assert (E : x * 16397105843297379215
              = x / 36 * 590295810358705651712 + (28 * (x / 36) + x mod 36 * 16397105843297379215)).
  { rewrite Hd at 1. ring. }
  rewrite E, Z.div_add_l by lia. rewrite (Z.div_small (28 * (x / 36) + x mod 36 * 16397105843297379215)) by lia.
  lia.
Qed.

Lemma shr64_range : forall x, 0 <= x < 2^64 -> 0 <= Z.shiftr (x * 16397105843297379215) 64 < 2^64.
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma sltiu_w : forall q, 0 <= q < 2^64 ->
  v_sltiu (Z_to_bv 64 (bv_swrap 32 (q + -41))) (-39)
  = Z_to_bv 64 (if (2 <=? q mod 2^32) && (q mod 2^32 <=? 40) then 0 else 1).
Proof.
  intros q Hq. unfold v_sltiu. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. change (bv_modulus 32) with 4294967296.
  change (bv_half_modulus 32) with 2147483648. change (2^32) with 4294967296.
  change (2^64) with 18446744073709551616 in Hq.
  destruct (Z.leb_spec 2 (q mod 4294967296)) as [A|A];
  destruct (Z.leb_spec (q mod 4294967296) 40) as [B|B]; cbn [andb];
  match goal with |- (if ?c then _ else _) = _ => destruct c eqn:L end; try reflexivity;
  exfalso; first [apply Z.ltb_lt in L | apply Z.ltb_ge in L]; Z.div_mod_to_equations; lia.
Qed.

Lemma lor_ones64 : forall q, 0 <= q < 2^64 -> Z.lor 18446744073709551615 q = 18446744073709551615.
Proof.
  intros q Hq. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 64) as [Li|Li].
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. cbn [orb].
    destruct (Z.eq_dec q 0) as [->|Hq0]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia].
Qed.

Lemma signed_wrap : forall z, bv_signed (Z_to_bv 64 z) = bv_swrap 64 z.
Proof. intros z. unfold bv_signed. rewrite Z_to_bv_unsigned. apply bv_swrap_wrap. Qed.

Lemma tail_bad : forall x q, 0 <= x < 2^64 -> Z.odd x = true -> 0 <= q < 2^64 ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr
    (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 63))) 63))) q)) + 0) = -1.
Proof.
  intros x q Hx Ho Hq.
  rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite signed_wrap.
  assert (S : bv_swrap 64 (x * 2^63) = - 2^63).
  { apply Z.odd_spec in Ho. destruct Ho as [k ->]. unfold bv_swrap, bv_wrap.
    change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
    replace ((2 * k + 1) * 2 ^ 63 + 2 ^ 63) with ((k + 1) * 2^64) by ring.
    rewrite Z.mod_mul by lia. lia. }
  rewrite S. change (Z.shiftr (- 2^63) 63) with (-1).
  replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615 by (vm_compute; reflexivity).
  rewrite lor_ones64 by lia.
  vm_compute. reflexivity.
Qed.

Lemma tail_good : forall q, 0 <= q < 2^64 -> Z.even q = true -> 2 <= q mod 2^32 <= 40 ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr
    (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 q)) 63))) 63))) q)) + 0) = q mod 2^32.
Proof.
  intros q Hq Ev Hw.
  rewrite (unsigned_lit q) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite signed_wrap.
  assert (S : bv_swrap 64 (q * 2^63) = 0).
  { apply Z.even_spec in Ev. destruct Ev as [k ->]. unfold bv_swrap, bv_wrap.
    change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
    replace (2 * k * 2 ^ 63 + 2 ^ 63) with (2^63 + k * 2^64) by ring.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  rewrite S. change (Z.shiftr 0 63) with 0.
  rewrite (unsigned_lit 0) by lia. rewrite Z.lor_0_l. rewrite (unsigned_lit q) by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^32) with 4294967296 in *. change (2^64) with 18446744073709551616 in Hq.
  Z.div_mod_to_equations. lia.
Qed.

Lemma even_mod32 : forall q, Z.even (q mod 2^32) = Z.even q.
Proof.
  intros q. rewrite (Z.div_mod q (2^32)) at 2 by lia.
  rewrite Z.even_add, Z.even_mul. change (Z.even (2^32)) with true. cbn [orb].
  destruct (Z.even (q mod 2^32)); reflexivity.
Qed.

Theorem reac_upstream_channels_holds : reac_upstream_channels_contract.
Proof.
  unfold reac_upstream_channels_contract, REAC_UPSTREAM_CHANNELS, UPSTREAM_DIV36_AT, UPSTREAM_DIV36.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HK.
  assert (RD : ov_read_bytes rsegs m (wa 0x103a0) 8 = Some (le8 (Z_to_bv 64 0xe38e38e38e38e38f))).
  { replace (wa 0x103a0) with (wa (0x103a0 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x103a0 _ 0 8 HK ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  step. step. step.
  if_cases HL.
  - zify_cond HL.
    step. step. apply evt_done.
    rewrite upstream_small by lia. do 3 eexists. reflexivity.
  - zify_cond HL.
    do 9 step.
    try rewrite (unsigned_lit 16397105843297379215) by lia.
    rewrite (unsigned_lit (bv_unsigned a0 + -52)) by lia.
    assert (Hx : 0 <= bv_unsigned a0 + -52 < 2^64) by lia.
    rewrite (unsigned_lit (Z.shiftr ((bv_unsigned a0 + -52) * 16397105843297379215) 64)) by (apply shr64_range; exact Hx).
    rewrite (div36_magic _ Hx).
    replace (bv_unsigned a0 + -52) with (bv_unsigned a0 - 52) in * by lia.
    pose proof (Z.div_mod (bv_unsigned a0 - 52) 36 ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (bv_unsigned a0 - 52) 36 ltac:(lia)) as MB.
    remember ((bv_unsigned a0 - 52) / 36) as q eqn:Eq.
    rewrite (unsigned_lit q) by lia.
    rewrite (unsigned_lit (q * 36)) by lia.
    if_cases HR.
    + zify_cond HR. try rewrite Z.mod_small in HR by lia.
      assert (U : upstream_result (bv_unsigned a0) = -1).
      { unfold upstream_result, upstream_ok.
        rewrite (proj2 (Z.leb_le 52 (bv_unsigned a0)) ltac:(lia)).
        rewrite (proj2 (Z.eqb_neq ((bv_unsigned a0 - 52) mod 36) 0) ltac:(lia)). reflexivity. }
      step. step. apply evt_done. rewrite U. do 3 eexists. reflexivity.
    + zify_cond HR.
      do 8 step. apply evt_done.
      rewrite !(unsigned_lit q) by lia.
      rewrite (sltiu_w q) by lia.
      assert (Ew : upstream_width (bv_unsigned a0) = q mod 2^32) by (unfold upstream_width; rewrite Eq; reflexivity).
      assert (Er : (bv_unsigned a0 - 52) mod 36 = 0) by lia.
      assert (L52 : (52 <=? bv_unsigned a0) = true) by (apply Z.leb_le; lia).
      assert (Hq : 0 <= q < 2^64) by lia.
      unfold upstream_result, upstream_ok. rewrite Ew, Er, L52, even_mod32.
      destruct (2 <=? q mod 2^32) eqn:C1; destruct (q mod 2^32 <=? 40) eqn:C2; destruct (Z.even q) eqn:EV;
        cbn [andb Z.eqb].
      * rewrite (unsigned_lit 0), Z.lor_0_l by lia.
        apply Z.leb_le in C1. apply Z.leb_le in C2.
        rewrite tail_good by (try assumption; lia). do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 0), Z.lor_0_l by lia.
        rewrite (tail_bad q q) by (try lia; rewrite <- Z.negb_even, EV; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
Qed.
