From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd BoxregUpd.
Import ListNotations.
Open Scope Z_scope.

Lemma bx_ov4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; lia).
  first [ reflexivity | f_equal; apply firstn_all2; rewrite length_le4; lia ].
Qed.

Lemma bx_byte1 : forall m p M j b, bytes_at rsegs m p M -> 0 <= j -> nth_error M (Z.to_nat j) = Some b ->
  ov_read_bytes rsegs m (wa (p + j)) 1 = Some [b].
Proof.
  intros m p M j b HB Hj Hn.
  assert (Hl : (Z.to_nat j < length M)%nat) by (apply nth_error_Some; congruence).
  rewrite (bytes_at_read rsegs m p M j 1 HB Hj) by lia.
  f_equal. destruct (nth_error_split M (Z.to_nat j) Hn) as (l1 & l2 & E & L1).
  rewrite E, <- L1, skipn_app_exact. reflexivity.
Qed.

Lemma bx_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma bx_signed : forall x, -2^63 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (18446744073709551616 / 2) with 9223372036854775808.
  change (2^63) with 9223372036854775808 in Hx. Z.div_mod_to_equations. lia.
Qed.

Lemma bx_lts : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !bx_signed by lia. reflexivity. Qed.

Lemma bx_ltu : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma bx_eqb : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in Hx, Hy.
  destruct (Z.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E'. apply E. Z.div_mod_to_equations. lia.
Qed.

Lemma bx_wtest : forall k, -2^31 <= k < 2^31 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 k) + -41))) (Z_to_bv 64 (-39)) =
  negb ((2 <=? k) && (k <=? 40)).
Proof.
  intros k Hk. unfold bv_ltu. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 / 2) with 2147483648. change (2^31) with 2147483648 in Hk.
  change ((-39) mod 18446744073709551616) with 18446744073709551577.
  destruct (Z.leb_spec 2 k); destruct (Z.leb_spec k 40); cbn [andb negb];
    apply Z.ltb_ge || apply Z.ltb_lt; Z.div_mod_to_equations; lia.
Qed.

Lemma bx_land1 : forall k, 0 <= k < 2^64 -> Z.land (bv_unsigned (Z_to_bv 64 k)) 1 = k mod 2.
Proof.
  intros k Hk. rewrite unsigned_lit by lia. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma bx_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma bx_zero6_nth : forall j b, nth_error zero6 j = Some b -> b = Z_to_bv 8 0.
Proof. intros j b H. apply nth_error_In in H. apply repeat_spec in H. exact H. Qed.

Lemma bx_zero6_of : forall M, length M = 6%nat -> (forall i, (i < 6)%nat -> nth_error M i = Some (Z_to_bv 8 0)) ->
  M = zero6.
Proof.
  intros M HL H. do 7 (destruct M as [|?b M]; cbn in HL; try discriminate).
  pose proof (H 0%nat ltac:(lia)) as E0; pose proof (H 1%nat ltac:(lia)) as E1; pose proof (H 2%nat ltac:(lia)) as E2;
  pose proof (H 3%nat ltac:(lia)) as E3; pose proof (H 4%nat ltac:(lia)) as E4; pose proof (H 5%nat ltac:(lia)) as E5.
  cbn in E0, E1, E2, E3, E4, E5. unfold zero6. cbn [repeat]. congruence.
Qed.

Lemma bx_off56 : forall i, 0 <= i <= 5 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 i)) 6)) -
  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 i)) 3)) = 56 * i.
Proof.
  intros i Hi. rewrite (unsigned_lit i) by lia. rewrite !Z.shiftl_mul_pow2 by lia. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma bx_swrap_z : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 0) = z.
Proof.
  intros z Hz. rewrite Z.add_0_r, unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Definition bx_keep (P : Prop) : Prop := P.

Lemma bx_rw_sub : forall m r bs a w, bytes_at rsegs m r bs -> wr_at rsegs m r (Z.of_nat (length bs)) ->
  0 <= a -> 0 <= w -> a + w <= Z.of_nat (length bs) ->
  rw_cells rsegs m (r + a) [CB (Z.to_nat w) (bsub bs a w)].
Proof.
  intros m r bs a w HB HW Ha Hw Hl. split; [split|].
  - cbn. split; [apply bsub_length; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_bsub; assumption.
  - cbn [cells_size csize]. destruct HW as (H0 & H1 & H2). split; [lia|]. split; [lia|].
    intros i Hi. replace (r + a + i) with (r + (a + i)) by lia. apply H2. lia.
Qed.

Lemma bx_rw_split : forall m A a b X, rw_cells rsegs m A [CB (a + b) X] ->
  rw_cells rsegs m A [CB a (firstn a X)] /\ rw_cells rsegs m (A + Z.of_nat a) [CB b (skipn a X)].
Proof.
  intros m A a b X [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [HX _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw.
  rewrite <- (firstn_skipn a X) in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2].
  rewrite length_firstn in Hb2. replace (Nat.min a (length X)) with a in Hb2 by lia.
  destruct Hw as (Hw0 & Hw1 & Hw2). split.
  - split; [split|].
    + cbn. split; [rewrite length_firstn; lia | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb1.
    + cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw2. lia.
  - split; [split|].
    + cbn. split; [rewrite length_skipn; lia | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb2.
    + cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat a + i) with (A + (Z.of_nat a + i)) by lia. apply Hw2. lia.
Qed.

Lemma bx_rw_app : forall m A cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[Hwf1 Hb1] Hw1] [[Hwf2 Hb2] Hw2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact Hb1|]. rewrite cells_bytes_length by exact Hwf1.
    exact Hb2.
  - rewrite cells_size_app. destruct Hw1 as (A0 & A1 & A2). destruct Hw2 as (B0 & B1 & B2).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [L|L]; [apply A2; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply B2. lia.
Qed.

Lemma bx_rw_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

Lemma bx_patch1 : forall m m' r bs W a x,
  bytes_at rsegs m r bs -> munch W m m' -> bytes_at rsegs m' (r + Z.of_nat a) x ->
  (a + length x <= length bs)%nat ->
  (forall i, (i < length bs)%nat -> ~ (a <= i < a + length x)%nat -> outside W (r + Z.of_nat i)) ->
  bytes_at rsegs m' r (upd_bytes bs a x).
Proof.
  intros m m' r bs W a x (H0 & H1 & H2) MU (X0 & X1 & X2) Hl Hout.
  unfold bytes_at. rewrite upd_bytes_length by exact Hl. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite upd_bytes_nth by assumption.
  destruct (Nat.leb_spec a i); destruct (Nat.ltb_spec i (a + length x)); cbn [andb].
  - rewrite <- X2 by lia. f_equal. f_equal. lia.
  - rewrite <- H2 by exact Hi. unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by lia. apply Hout; lia.
  - rewrite <- H2 by exact Hi. unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by lia. apply Hout; lia.
  - rewrite <- H2 by exact Hi. unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by lia. apply Hout; lia.
Qed.

Lemma bx_patch2 : forall m m' r bs W a1 x1 a2 x2,
  bytes_at rsegs m r bs -> munch W m m' ->
  bytes_at rsegs m' (r + Z.of_nat a1) x1 -> bytes_at rsegs m' (r + Z.of_nat a2) x2 ->
  (a1 + length x1 <= a2)%nat -> (a2 + length x2 <= length bs)%nat ->
  (forall i, (i < length bs)%nat -> ~ (a1 <= i < a1 + length x1)%nat -> ~ (a2 <= i < a2 + length x2)%nat ->
     outside W (r + Z.of_nat i)) ->
  bytes_at rsegs m' r (upd_bytes (upd_bytes bs a1 x1) a2 x2).
Proof.
  intros m m' r bs W a1 x1 a2 x2 (H0 & H1 & H2) MU (X0 & X1 & X2) (Y0 & Y1 & Y2) Hl1 Hl2 Hout.
  assert (L1 : length (upd_bytes bs a1 x1) = length bs) by (apply upd_bytes_length; lia).
  unfold bytes_at. rewrite upd_bytes_length by lia. rewrite L1. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite upd_bytes_nth by lia.
  destruct (Nat.leb_spec a2 i); destruct (Nat.ltb_spec i (a2 + length x2)); cbn [andb];
    [ rewrite <- Y2 by lia; f_equal; f_equal; lia | | | ];
  rewrite upd_bytes_nth by lia;
  (destruct (Nat.leb_spec a1 i); destruct (Nat.ltb_spec i (a1 + length x1)); cbn [andb];
    [ rewrite <- X2 by lia; f_equal; f_equal; lia
    | rewrite <- H2 by exact Hi; unfold mrd; rewrite MU; [reflexivity|]; rewrite wa_unsigned by lia; apply Hout; lia
    | rewrite <- H2 by exact Hi; unfold mrd; rewrite MU; [reflexivity|]; rewrite wa_unsigned by lia; apply Hout; lia
    | rewrite <- H2 by exact Hi; unfold mrd; rewrite MU; [reflexivity|]; rewrite wa_unsigned by lia; apply Hout; lia ]).
Qed.

Lemma bx_even : forall k, Z.even k = true <-> k mod 2 = 0.
Proof.
  intros k. rewrite Z.even_spec. split.
  - intros [q ->]. rewrite Z.mul_comm. apply Z_mod_mult.
  - intros H. exists (k / 2). pose proof (Z.div_mod k 2 ltac:(lia)). lia.
Qed.

Lemma bx_firstn_repeat : forall {A} (x : A) a b, firstn a (repeat x (a + b)) = repeat x a.
Proof. intros A x a. induction a as [|a IH]; intros b; [reflexivity|]. cbn. f_equal. apply IH. Qed.

Lemma bx_skipn_repeat : forall {A} (x : A) a b, skipn a (repeat x (a + b)) = repeat x b.
Proof. intros A x a. induction a as [|a IH]; intros b; [reflexivity|]. cbn. apply IH. Qed.

Lemma bx_skipn_repeat_gen : forall {A} (x : A) a n, skipn a (repeat x n) = repeat x (n - a).
Proof.
  intros A x a. induction a as [|a IH]; intros n; [cbn; rewrite Nat.sub_0_r; reflexivity|].
  destruct n as [|n]; [reflexivity|]. cbn. apply IH.
Qed.

Lemma bx_land3 : forall k, 0 <= k < 2^64 -> Z.land (bv_unsigned (Z_to_bv 64 k)) 3 = k mod 4.
Proof.
  intros k Hk. rewrite unsigned_lit by lia. change 3 with (Z.ones 2) at 1. rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma bx_lxor_ltu : forall r x, 0 <= r < 2^64 -> 0 <= x -> r + x < 2^64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 r)) 18446744073709551615)) (Z_to_bv 64 x) = false.
Proof.
  intros r x Hr Hx Hrx. rewrite (unsigned_lit r) by lia. rewrite zb_lxor_ones by lia.
  unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
Qed.

Lemma bx_task_wview : forall m a, MemNorm.task_mem rsegs m -> wview rsegs m a <> None ->
  find_segment rsegs (bv_unsigned a) 1 <> None \/ bv_unsigned a < TASK_SIZE.
Proof.
  intros m a T W. unfold wview in W. destruct (m a) as [b|] eqn:E.
  - exact (T a b E).
  - destruct (find_segment rsegs (bv_unsigned a) 1) eqn:F; [left; discriminate | congruence].
Qed.

Lemma bx_task_munch2 : forall m m' lo S r,
  MemNorm.task_mem rsegs m -> munch [(lo, S); (r, r + 288)] m m' ->
  stk rsegs m lo S -> wr_at rsegs m r 288 -> MemNorm.task_mem rsegs m'.
Proof.
  intros m m' lo S r T MU ST HW a b E.
  pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
  assert (Ea : wa (bv_unsigned a) = a) by (apply bv_eq; rewrite wa_unsigned by lia; reflexivity).
  assert (D : (lo <= bv_unsigned a < S) \/ (r <= bv_unsigned a < r + 288) \/
              (~ (lo <= bv_unsigned a < S) /\ ~ (r <= bv_unsigned a < r + 288))) by lia.
  destruct D as [D|[D|[D1 D2]]].
  - destruct (proj2 (proj2 ST) (bv_unsigned a) D) as [Wv _]. rewrite Ea in Wv. exact (bx_task_wview m a T Wv).
  - destruct HW as (_ & _ & HW'). specialize (HW' (bv_unsigned a - r) ltac:(lia)).
    replace (r + (bv_unsigned a - r)) with (bv_unsigned a) in HW' by lia. rewrite Ea in HW'.
    exact (bx_task_wview m a T HW').
  - rewrite (MU a) in E by (cbn [outside]; tauto). exact (T a b E).
Qed.
