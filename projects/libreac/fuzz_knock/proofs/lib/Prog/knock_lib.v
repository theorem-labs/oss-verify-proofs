From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hl, Hw.
  rewrite cells_bytes_length in B2 by exact W1.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma rw_cells_app_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma bytes_at_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma mem_inv_from_entry : forall m m' lo hi k,
  mem_inv rsegs m -> stk rsegs m lo hi -> lo <= hi - k -> munch [(hi - k, hi)] m m' -> mem_inv rsegs m'.
Proof.
  intros m m' lo hi k HI ST Hk MU x b Hx.
  pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
  destruct (Z.ltb_spec (bv_unsigned x) (hi - k)) as [Hlt | Hge];
  [ | destruct (Z.ltb_spec (bv_unsigned x) hi) as [Hlt2 | Hge2] ].
  - rewrite (MU x) in Hx by (cbn [outside]; split; [lia | exact I]). exact (HI x b Hx).
  - destruct ST as (Hlo & Hhi & HS). destruct (HS (bv_unsigned x) ltac:(lia)) as [Hw _].
    unfold wa in Hw. rewrite (Z_to_bv_bv_unsigned x) in Hw.
    destruct (m x) as [b0|] eqn:Em.
    + exact (HI x b0 Em).
    + exact (wview_not_ro rsegs m x Hw Em).
  - rewrite (MU x) in Hx by (cbn [outside]; split; [lia | exact I]). exact (HI x b Hx).
Qed.

Lemma lor_lt_2_16 : forall x y, 0 <= x < 2 ^ 16 -> 0 <= y < 2 ^ 16 -> 0 <= Z.lor x y < 2 ^ 16.
Proof.
  intros x y Hx Hy. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor x y) 0) as [E|E]; [lia|].
  assert (Hpos : 0 < Z.lor x y) by (pose proof (Z.lor_nonneg x y); lia).
  pose proof (Z.log2_spec (Z.lor x y) Hpos) as [_ Hup].
  rewrite Z.log2_lor in Hup by lia.
  assert (Lx : Z.log2 x < 16) by (destruct (Z.eq_dec x 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
  assert (Ly : Z.log2 y < 16) by (destruct (Z.eq_dec y 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
  assert (2 ^ Z.succ (Z.max (Z.log2 x) (Z.log2 y)) <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Lemma dt_bound : forall x y z, 0 <= x < 2 ^ 16 -> 0 <= y < 2 ^ 16 ->
  0 <= Z.shiftl (Z.lor x y) (Z.shiftr (z mod 2 ^ 64) 61 mod 64) < 2 ^ 23.
Proof.
  intros x y z Hx Hy.
  assert (Hz : 0 <= z mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (Hs : 0 <= Z.shiftr (z mod 2 ^ 64) 61 < 8).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (Z.mod_small (Z.shiftr (z mod 2 ^ 64) 61) 64) by lia.
  pose proof (lor_lt_2_16 x y Hx Hy) as Hl.
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (2 ^ Z.shiftr (z mod 2 ^ 64) 61 <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia).
  assert (0 < 2 ^ Z.shiftr (z mod 2 ^ 64) 61) by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.

Lemma lor_lt_pow : forall x y n, 0 < n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lor x y < 2 ^ n.
Proof.
  intros x y n Hn Hx Hy. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor x y) 0) as [E|E]; [pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)); lia|].
  assert (Hpos : 0 < Z.lor x y) by (pose proof (Z.lor_nonneg x y); lia).
  pose proof (Z.log2_spec (Z.lor x y) Hpos) as [_ Hup].
  rewrite Z.log2_lor in Hup by lia.
  assert (Lx : Z.log2 x < n).
  { destruct (Z.eq_dec x 0) as [Ex|Ex]; [subst x; rewrite Z.log2_nonpos by lia; lia | apply Z.log2_lt_pow2; lia]. }
  assert (Ly : Z.log2 y < n).
  { destruct (Z.eq_dec y 0) as [Ey|Ey]; [subst y; rewrite Z.log2_nonpos by lia; lia | apply Z.log2_lt_pow2; lia]. }
  assert (2 ^ Z.succ (Z.max (Z.log2 x) (Z.log2 y)) <= 2 ^ n) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.
