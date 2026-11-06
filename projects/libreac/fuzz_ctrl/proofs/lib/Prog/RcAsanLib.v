From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsan.
Import ListNotations.
Open Scope Z_scope.

Lemma rc_bytes_at_munch : forall segs W m m' A bs,
  bytes_at segs m A bs -> munch W m m' ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> outside W x) ->
  bytes_at segs m' A bs.
Proof.
  intros segs W m m' A bs (Ha & Hl & H) Hm Ho. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hm.
  - apply H. exact Hi.
  - rewrite wa_unsigned by lia. apply Ho. lia.
Qed.

Lemma asan_rt_munch : forall segs m m' gotK cellK off W W',
  asan_rt segs m gotK cellK off W -> munch W' m m' -> sub_fp W' W -> asan_rt segs m' gotK cellK off W.
Proof.
  intros segs m m' gotK cellK off W W' (Hg & Hc & Dg & Dc) Hm Hs.
  split; [|split; [|split; assumption]].
  - eapply rc_bytes_at_munch; [exact Hg | exact Hm |].
    intros x Hx. rewrite length_le8 in Hx. apply Hs. apply Dg. lia.
  - eapply rc_bytes_at_munch; [exact Hc | exact Hm |].
    intros x Hx. rewrite length_le8 in Hx. apply Hs. apply Dc. lia.
Qed.

Lemma asan_shadow_rd_munch : forall segs m m' off a n W W',
  asan_shadow_rd segs m off a n W -> munch W' m m' -> sub_fp W' W -> asan_shadow_rd segs m' off a n W.
Proof.
  intros segs m m' off a n W W' H Hm Hs i Hi. destruct (H i Hi) as [Ho [k Hk]].
  split; [exact Ho|]. exists k. eapply rc_bytes_at_munch; [exact Hk | exact Hm |].
  intros x Hx. cbn [length] in Hx. replace x with (asan_shadow off (a + i)) by lia. apply Hs. exact Ho.
Qed.

Lemma asan_addressable_munch : forall segs m m' off a n W W',
  asan_addressable segs m off a n -> asan_shadow_rd segs m off a n W -> munch W' m m' -> sub_fp W' W ->
  asan_addressable segs m' off a n.
Proof.
  intros segs m m' off a n W W' HA HR Hm Hs i k Hi Hk.
  destruct (HR i Hi) as [Ho [k0 Hk0]].
  assert (Hk0' : bytes_at segs m' (asan_shadow off (a + i)) [k0]).
  { eapply rc_bytes_at_munch; [exact Hk0 | exact Hm |].
    intros x Hx. cbn [length] in Hx. replace x with (asan_shadow off (a + i)) by lia. apply Hs. exact Ho. }
  assert (E : k = k0).
  { destruct Hk as (_ & _ & E1). destruct Hk0' as (_ & _ & E2).
    specialize (E1 0%nat ltac:(cbn; lia)). specialize (E2 0%nat ltac:(cbn; lia)).
    rewrite E2 in E1. cbn in E1. congruence. }
  subst k. exact (HA i k0 Hi Hk0).
Qed.

Lemma rc_byte1_eq : forall segs m A (k k0 : byte), bytes_at segs m A [k] -> bytes_at segs m A [k0] -> k = k0.
Proof.
  intros segs m A k k0 (_ & _ & E1) (_ & _ & E2).
  specialize (E1 0%nat ltac:(cbn; lia)). specialize (E2 0%nat ltac:(cbn; lia)).
  rewrite E2 in E1. cbn in E1. congruence.
Qed.

Lemma asan_rt3_munch : forall segs m m' off a n W W',
  asan_rt3 segs m off a n -> asan_shadow_rd segs m off a n W -> munch W' m m' -> sub_fp W' W ->
  asan_rt3 segs m' off a n.
Proof.
  intros segs m m' off a n W W' H3 HR Hm Hs i k Hi Hk.
  destruct (HR i Hi) as [Ho [k0 Hk0]].
  assert (Hk0' : bytes_at segs m' (asan_shadow off (a + i)) [k0]).
  { eapply rc_bytes_at_munch; [exact Hk0 | exact Hm |].
    intros x Hx. cbn [length] in Hx. replace x with (asan_shadow off (a + i)) by lia. apply Hs. exact Ho. }
  rewrite (rc_byte1_eq segs m' _ k k0 Hk Hk0'). exact (H3 i k0 Hi Hk0).
Qed.

Lemma asan_shadow_same : forall off a j, 0 <= j -> a mod 8 + j < 8 ->
  asan_shadow off (a + j) = asan_shadow off a /\ (a + j) mod 8 = a mod 8 + j.
Proof. intros off a j Hj Hw. unfold asan_shadow. split; Z.div_mod_to_equations; lia. Qed.

Lemma asan_check_lt : forall segs m off a n i w (k : byte),
  asan_addressable segs m off a n -> 0 <= i -> 1 <= w -> i + w <= n -> (a + i) mod 8 + w <= 8 ->
  bytes_at segs m (asan_shadow off (a + i)) [k] ->
  bv_signed k = 0 \/ (a + i) mod 8 + (w - 1) < bv_signed k.
Proof.
  intros segs m off a n i w k HA Hi Hw Hn Hm Hk.
  destruct (asan_shadow_same off (a + i) (w - 1) ltac:(lia) ltac:(lia)) as [E1 E2].
  assert (Hk' : bytes_at segs m (asan_shadow off (a + (i + (w - 1)))) [k]).
  { replace (a + (i + (w - 1))) with (a + i + (w - 1)) by lia. rewrite E1. exact Hk. }
  pose proof (HA (i + (w - 1)) k ltac:(lia) Hk') as OK. unfold asan_ok in OK.
  replace (a + (i + (w - 1))) with (a + i + (w - 1)) in OK by lia. rewrite E2 in OK. exact OK.
Qed.

Lemma asan_check_8 : forall segs m off a n i (k : byte),
  asan_addressable segs m off a n -> asan_rt3 segs m off a n -> 0 <= i -> i + 8 <= n -> (a + i) mod 8 = 0 ->
  bytes_at segs m (asan_shadow off (a + i)) [k] -> bv_signed k = 0.
Proof.
  intros segs m off a n i k HA H3 Hi Hn Hm Hk.
  pose proof (H3 i k ltac:(lia) Hk) as L.
  destruct (asan_check_lt segs m off a n i 8 k HA Hi ltac:(lia) Hn ltac:(lia) Hk) as [E|E]; lia.
Qed.

Lemma rc_signed0_unsigned0 : forall k : byte, bv_signed k = 0 -> bv_unsigned k = 0.
Proof.
  intros k H. pose proof (bv_unsigned_in_range 8 k) as R. unfold bv_modulus in R. cbn in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 8 / 2) with 128 in H. change (2 ^ Z.of_N 8) with 256 in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma asan_shadow_read_at : forall segs m off a n W i A,
  asan_shadow_rd segs m off a n W -> 0 <= i < n -> A = asan_shadow off (a + i) ->
  exists k : byte, ov_read_bytes segs m (wa A) 1 = Some [k] /\ bytes_at segs m (asan_shadow off (a + i)) [k].
Proof.
  intros segs m off a n W i A H Hi ->. destruct (H i Hi) as [_ [k Hk]]. exists k. split; [|exact Hk].
  replace (wa (asan_shadow off (a + i))) with (wa (asan_shadow off (a + i) + 0)) by (f_equal; lia).
  rewrite (bytes_at_read segs m _ [k] 0 1 Hk) by (cbn; lia).
  reflexivity.
Qed.

Lemma asan_rt_got_read : forall segs m gotK cellK off W,
  asan_rt segs m gotK cellK off W -> ov_read_bytes segs m (wa gotK) 8 = Some (le8 (Z_to_bv 64 cellK)).
Proof.
  intros segs m gotK cellK off W (Hg & _).
  replace (wa gotK) with (wa (gotK + 0)) by (f_equal; lia).
  rewrite (bytes_at_read segs m gotK _ 0 8 Hg) by (rewrite ?length_le8; lia).
  reflexivity.
Qed.

Lemma asan_rt_cell_read : forall segs m gotK cellK off W,
  asan_rt segs m gotK cellK off W -> ov_read_bytes segs m (wa cellK) 8 = Some (le8 (Z_to_bv 64 off)).
Proof.
  intros segs m gotK cellK off W (_ & Hc & _).
  replace (wa cellK) with (wa (cellK + 0)) by (f_equal; lia).
  rewrite (bytes_at_read segs m cellK _ 0 8 Hc) by (rewrite ?length_le8; lia).
  reflexivity.
Qed.

Lemma asan_shadow_read : forall segs m off a n W i,
  asan_shadow_rd segs m off a n W -> 0 <= i < n ->
  exists k : byte, ov_read_bytes segs m (wa ((a + i) / 8 + off)) 1 = Some [k] /\
                   bytes_at segs m (asan_shadow off (a + i)) [k].
Proof.
  intros segs m off a n W i H Hi. destruct (H i Hi) as [_ [k Hk]]. exists k. split; [|exact Hk].
  replace (wa ((a + i) / 8 + off)) with (wa (asan_shadow off (a + i) + 0)) by (unfold asan_shadow; f_equal; lia).
  rewrite (bytes_at_read segs m _ [k] 0 1 Hk) by (cbn; lia).
  reflexivity.
Qed.

Lemma rc_signed_lit : forall x, -2^63 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit_wrap. destruct (Z.leb_spec 0 x).
  - rewrite Z.mod_small by lia. replace (x <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - rewrite <- (Z.mod_add x 1) by lia. rewrite Z.mod_small by lia.
    replace (x + 1 * 2^64 <? 2^63) with false by (symmetry; apply Z.ltb_ge; lia). lia.
Qed.

Lemma rc_byte_signed : forall k : byte, -128 <= bv_signed k < 128.
Proof.
  intros k. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8 / 2) with 128. change (2 ^ Z.of_N 8) with 256.
  pose proof (Z.mod_pos_bound (bv_unsigned k + 128) 256 ltac:(lia)). lia.
Qed.

Lemma rc_eqb0_signed : forall x, -2^63 <= x < 2^63 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec x 0) as [->|E]; [reflexivity|]. apply Z.eqb_neq. intros E'. apply E.
  destruct (Z.leb_spec 0 x).
  - rewrite Z.mod_small in E' by lia. exact E'.
  - rewrite <- (Z.mod_add x 1) in E' by lia. rewrite Z.mod_small in E' by lia. lia.
Qed.

Lemma rc_lts_signed : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !rc_signed_lit by assumption. reflexivity. Qed.

Lemma rc_neq0_64 : forall x, 0 < x < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof. intros x Hx. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma rc_ltu_lit64 : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rc_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. exact (zb_land_mask x 3 ltac:(lia)). Qed.

Lemma rc_shr3 : forall x, Z.shiftr x 3 = x / 8.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma rc_mem_inv_frame : forall segs m m' a b,
  mem_inv segs m -> munch [(a, b)] m m' ->
  (forall x, a <= x < b -> wview segs m (wa x) <> None) ->
  mem_inv segs m'.
Proof.
  intros segs m m' a b Hinv Hm Hw x v Hx.
  destruct (Z.leb_spec a (bv_unsigned x)) as [L1|L1];
    [destruct (Z.ltb_spec (bv_unsigned x) b) as [L2|L2]|].
  - assert (W : wview segs m x <> None).
    { replace x with (wa (bv_unsigned x))
        by (first [apply wa_of_var; reflexivity | symmetry; apply wa_of_var; reflexivity]).
      apply Hw. lia. }
    destruct (m x) as [v0|] eqn:E.
    + exact (Hinv x v0 E).
    + exact (wview_not_ro segs m x W E).
  - rewrite (Hm x) in Hx by (split; [lia | exact I]). exact (Hinv x v Hx).
  - rewrite (Hm x) in Hx by (split; [lia | exact I]). exact (Hinv x v Hx).
Qed.

Lemma rc_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z.le_gt_cases lo x); destruct (Z.lt_ge_cases x hi).
    + right. intros [Hin _]. lia.
    + left. split; [lia|exact H].
    + left. split; [lia|exact H].
    + left. split; [lia|exact H].
  - right. intros [_ H2]. exact (H H2).
Qed.

Lemma rc_mem_inv_munch : forall segs W m m',
  mem_inv segs m -> munch W m m' ->
  (forall x, ~ outside W x -> wview segs m (wa x) <> None) ->
  mem_inv segs m'.
Proof.
  intros segs W m m' Hinv Hm Hw x v Hx.
  destruct (rc_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (Hm x Ho) in Hx. exact (Hinv x v Hx).
  - assert (W0 : wview segs m x <> None).
    { replace x with (wa (bv_unsigned x))
        by (first [apply wa_of_var; reflexivity | symmetry; apply wa_of_var; reflexivity]).
      apply Hw. exact Ho. }
    destruct (m x) as [v0|] eqn:E.
    + exact (Hinv x v0 E).
    + exact (wview_not_ro segs m x W0 E).
Qed.

Lemma rc_not_outside_cons : forall lo hi W x, ~ outside ((lo, hi) :: W) x -> (lo <= x < hi) \/ ~ outside W x.
Proof.
  intros lo hi W x H. destruct (Z.le_gt_cases lo x) as [H1|H1]; destruct (Z.lt_ge_cases x hi) as [H2|H2].
  - left. lia.
  - right. intros Ho. apply H. cbn. split; [lia | exact Ho].
  - right. intros Ho. apply H. cbn. split; [lia | exact Ho].
  - right. intros Ho. apply H. cbn. split; [lia | exact Ho].
Qed.

Lemma rc_not_outside_nil : forall x, ~ outside [] x -> False.
Proof. intros x H. apply H. exact I. Qed.

Lemma rc_wv_stk : forall segs m lo hi x, stk segs m lo hi -> lo <= x < hi -> wview segs m (wa x) <> None.
Proof. intros segs m lo hi x (_ & _ & H) Hx. exact (proj1 (H x Hx)). Qed.

Lemma rc_wv_wr : forall segs m c n x, wr_at segs m c n -> c <= x < c + n -> wview segs m (wa x) <> None.
Proof.
  intros segs m c n x (_ & _ & H) Hx. replace x with (c + (x - c)) by lia. apply H. lia.
Qed.
