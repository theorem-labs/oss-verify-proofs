(* LLVMFuzzerTestOneInput_segX_up_arith: the arithmetic the image-B `up` segment of
   LLVMFuzzerTestOneInput (+0x840..+0x968, lib/B/Prog/LLVMFuzzerTestOneInput_segG.v) needs and nothing else.

   The harness recomputes the upstream channel count in line at +0x844..+0x89c and compares it with what
   reac_upstream_channels returned (+0x8a0, whose taken edge is the abort block +0xb88). The in-line form divides
   by 36 with the image's magic multiplier: `ld a1, %lo(decodeb_obj 9)` (+0x854, the 8-byte read-only word
   0x10338 = UPSTREAM_DIV36_AT, value 0xe38e38e38e38e38f), `mulhu` (+0x85c) and `srli 5` (+0x860), i.e.
   x * M / 2 ^ 69. up_div36 says that is x / 36 over the whole range the slot pre allows (n < 2 ^ 26); the values
   of the engine's expressions built on it are lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_den.v.

   The segment also passes the count to reac_upstream_decode, whose model names it up_nch; up_nch_result says the
   two models agree, which is what ties llvm_b_st_96c's dec_b_uolen (CChan.upstream_result ..) to the leaf's
   up_nch (..). The uolen facts are the buffer size malloc is asked for at +0x8c0 and the scan loop L5 reads.

   The bounds are written as literals, not as powers, because this unit's lia cannot evaluate 2 ^ k. *)
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_upstream_channels_c reac_upstream_decode_c.
Open Scope Z_scope.

(* The slot pre's bound on the input length, as a literal: 2 ^ 26. *)
Definition UP_NMAX : Z := 67108864.
(* 2 ^ 69 and 2 ^ 64, as literals. *)
Definition UP_P69 : Z := 590295810358705651712.
Definition UP_P64 : Z := 18446744073709551616.

(* +0x85c / +0x860: mulhu then srli 5, i.e. the high 64 bits of x * M shifted right by 5. *)
Definition up_mulsh (x : Z) : Z := x * UPSTREAM_DIV36 / 2 ^ 64 / 32.

(* 36 * M = 2 ^ 69 + 28: the multiplier is the smallest one above 2 ^ 69 / 36. *)
Lemma up_div36_cell : 36 * UPSTREAM_DIV36 = UP_P69 + 28.
Proof. unfold UPSTREAM_DIV36, UP_P69. reflexivity. Qed.

(* The quotient's range over the inputs the slot pre allows, as linear facts about x / 36. *)
Lemma up_q_range : forall x, 0 <= x < UP_NMAX -> 0 <= x / 36 <= 1864135.
Proof.
intros x Hx. unfold UP_NMAX in Hx.
pose proof (Z.div_mod x 36 ltac:(discriminate)) as Hd.
pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as Hr.
lia.
Qed.

Lemma up_div36 : forall x, 0 <= x < UP_NMAX -> x * UPSTREAM_DIV36 / UP_P69 = x / 36.
Proof.
intros x Hx.
pose proof (up_q_range x Hx) as Hq. unfold UP_NMAX in Hx.
pose proof (Z.div_mod x 36 ltac:(discriminate)) as Hd.
pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as Hr.
assert (E : x * UPSTREAM_DIV36 = (x / 36) * UP_P69 + ((x / 36) * 28 + (x mod 36) * UPSTREAM_DIV36)).
{ replace (x * UPSTREAM_DIV36) with ((36 * (x / 36) + x mod 36) * UPSTREAM_DIV36)
    by (rewrite <- Hd; reflexivity).
  unfold UPSTREAM_DIV36, UP_P69. ring. }
rewrite E.
rewrite (Z.div_add_l (x / 36) UP_P69 ((x / 36) * 28 + (x mod 36) * UPSTREAM_DIV36)
          ltac:(unfold UP_P69; discriminate)).
rewrite (Z.div_small ((x / 36) * 28 + (x mod 36) * UPSTREAM_DIV36) UP_P69).
- lia.
- unfold UPSTREAM_DIV36, UP_P69. lia.
Qed.

(* The two shifts of the machine are one division by 2 ^ 69. *)
Lemma up_mulsh_div : forall x, up_mulsh x = x * UPSTREAM_DIV36 / UP_P69.
Proof.
intros x. unfold up_mulsh.
rewrite Z.div_div by (vm_compute; first [reflexivity | discriminate]).
replace (2 ^ 64 * 32) with UP_P69 by (unfold UP_P69; vm_compute; reflexivity).
reflexivity.
Qed.

Lemma up_mulsh_eq : forall x, 0 <= x < UP_NMAX -> up_mulsh x = x / 36.
Proof. intros x Hx. rewrite up_mulsh_div. exact (up_div36 x Hx). Qed.

(* +0x864..+0x86c: a2 = x - 36 * q is the remainder, which +0x874 tests against zero. *)
Lemma up_rem : forall x, 0 <= x < UP_NMAX -> x - 36 * up_mulsh x = x mod 36.
Proof.
intros x Hx. rewrite (up_mulsh_eq x Hx).
pose proof (Z.div_mod x 36 ltac:(discriminate)) as Hd. lia.
Qed.

(* +0x878..+0x880: `addiw a2,a1,-2` then `bltu a3,a2` at a3 = 38. The in-line count is refused unless the
   quotient is in [2, 40]; the test is unsigned on the sign-extended 32-bit q - 2. *)
Lemma up_range_test : forall q, 0 <= q <= 1864135 ->
  ((q - 2) mod UP_P64 <=? 38) = ((2 <=? q) && (q <=? 40))%bool.
Proof.
intros q Hq. unfold UP_P64.
destruct (Z.ltb_spec q 2) as [Hlt | Hge].
- assert (Hm : (q - 2) mod 18446744073709551616 = q - 2 + 1 * 18446744073709551616).
  { rewrite <- (Z.mod_add (q - 2) 1 18446744073709551616) by discriminate.
    apply Z.mod_small. lia. }
  rewrite Hm.
  replace (2 <=? q) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [andb]. apply Z.leb_gt. lia.
- rewrite (Z.mod_small (q - 2) 18446744073709551616) by lia.
  replace (2 <=? q) with true by (symmetry; apply Z.leb_le; lia).
  cbn [andb].
  destruct (Z.leb_spec q 40) as [H40 | H40]; [apply Z.leb_le; lia | apply Z.leb_gt; lia].
Qed.

Lemma up_mod2_even : forall q, (q mod 2 =? 0) = Z.even q.
Proof. intros q. rewrite Zmod_even. destruct (Z.even q); reflexivity. Qed.

(* +0x884..+0x890: `andi a0,a1,1`, `sltiu a0,a0,1`, `addi a0,a0,-1`, `or a0,a0,a1` is q when q is even and
   all ones when it is odd. Z.land q 1 is the machine's andi on a non-negative q. *)
Lemma up_land1_mod2 : forall q, 0 <= q -> Z.land q 1 = q mod 2.
Proof.
intros q Hq. change 1 with (Z.ones 1).
rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma up_even_land : forall q, 0 <= q -> (Z.land q 1 =? 0) = Z.even q.
Proof. intros q Hq. rewrite (up_land1_mod2 q Hq). apply up_mod2_even. Qed.

Lemma up_width_small : forall len, 0 <= len < UP_NMAX -> 52 <= len ->
  upstream_width len = (len - 52) / 36.
Proof.
intros len Hlen H52. unfold upstream_width.
pose proof (up_q_range (len - 52) ltac:(unfold UP_NMAX in *; lia)) as Hq.
rewrite (Z.mod_small ((len - 52) / 36) (2 ^ 32)); [reflexivity|].
change (2 ^ 32) with 4294967296. lia.
Qed.

(* reac_upstream_decode's own model of the count is reac_upstream_channels' model, so the segment may read the
   one llvm_b_st_840 states and hand the leaf the one its post is written in. *)
Lemma up_nch_result : forall len, 0 <= len < UP_NMAX -> up_nch len = upstream_result len.
Proof.
intros len Hlen. pose proof Hlen as Hlit. unfold UP_NMAX in Hlit.
unfold up_nch, upstream_result, upstream_ok.
destruct (Z.ltb_spec len 52) as [Hlt | H52].
- replace (52 <=? len) with false by (symmetry; apply Z.leb_gt; lia).
  replace (124 <=? len) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [andb]. reflexivity.
- replace (52 <=? len) with true by (symmetry; apply Z.leb_le; lia).
  cbn [andb].
  pose proof (up_q_range (len - 52) ltac:(unfold UP_NMAX; lia)) as Hq.
  pose proof (Z.div_mod (len - 52) 36 ltac:(discriminate)) as Hd.
  pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)) as Hrb.
  rewrite (up_width_small len Hlen H52), up_mod2_even.
  destruct (Z.eqb_spec ((len - 52) mod 36) 0) as [Hr0 | Hr0].
  + replace (124 <=? len) with (2 <=? (len - 52) / 36)
      by (destruct (Z.leb_spec 2 ((len - 52) / 36)) as [H2 | H2];
          [symmetry; apply Z.leb_le; lia | symmetry; apply Z.leb_gt; lia]).
    cbn [andb].
    destruct (2 <=? (len - 52) / 36);
    destruct (Z.even ((len - 52) / 36));
    destruct (Z.leb_spec ((len - 52) / 36) 40) as [H40 | H40];
    cbn [andb]; reflexivity.
  + replace ((len - 52) mod 36 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr0).
    rewrite !Bool.andb_false_r. cbn [andb].
    destruct (124 <=? len); cbn [andb]; reflexivity.
Qed.

(* The buffer size the harness asks malloc for at +0x8c0 (36 * count, or 1 when the count is not positive), and
   its bounds. *)
Definition up_olen (r : Z) : Z := if 0 <? r then 36 * r else 1.

Lemma up_result_cases : forall len, 0 <= len < UP_NMAX ->
  upstream_result len = -1 \/
  (upstream_result len = (len - 52) / 36 /\ 2 <= (len - 52) / 36 <= 40 /\
   Z.even ((len - 52) / 36) = true).
Proof.
intros len Hlen. unfold upstream_result.
destruct (upstream_ok len) eqn:Hok; [|left; reflexivity].
right. unfold upstream_ok in Hok.
apply andb_prop in Hok as [Hok H40]. apply andb_prop in Hok as [Hok H2].
apply andb_prop in Hok as [Hok Hev]. apply andb_prop in Hok as [H52 _].
apply Z.leb_le in H40. apply Z.leb_le in H2. apply Z.leb_le in H52.
rewrite (up_width_small len Hlen H52) in H40, H2, Hev.
split; [exact (up_width_small len Hlen H52) | split; [lia | exact Hev]].
Qed.

Lemma up_olen_bounds : forall len, 0 <= len < UP_NMAX ->
  1 <= up_olen (upstream_result len) <= 1440.
Proof.
intros len Hlen. unfold up_olen.
destruct (up_result_cases len Hlen) as [H1 | (Hq & Hr & _)].
- rewrite H1. cbn. lia.
- rewrite Hq. replace (0 <? (len - 52) / 36) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

