From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
Import ListNotations.
Open Scope Z_scope.

Definition meta_kept (m m' : word -> option byte) : Prop :=
  forall a, in_shadow a -> mrd rsegs m' (wa a) = mrd rsegs m (wa a).

Definition app_ivl (lo hi : Z) : Prop := forall a, lo <= a < hi -> app_mem a.

Lemma meta_kept_trans : forall m1 m2 m3, meta_kept m1 m2 -> meta_kept m2 m3 -> meta_kept m1 m3.
Proof. intros m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). apply H1, Ha. Qed.

Lemma in_shadow_range : forall a, in_shadow a -> 0 <= a /\ a + 1 <= 2^64.
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros; lia. Qed.

Lemma app_not_shadow : forall a, app_mem a -> in_shadow a -> False.
Proof. unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. intros; lia. Qed.

Lemma shadow_of_app : forall a, app_mem a -> in_shadow (shadow_addr a).
Proof.
  unfold app_mem, in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END.
  intros a H. Z.div_mod_to_equations. lia.
Qed.

Lemma app_ivl_meta : forall lo hi x, app_ivl lo hi -> in_shadow x -> x < lo \/ hi <= x.
Proof.
  intros lo hi x H Hx. destruct (Z_lt_le_dec x lo); [left; lia|]. destruct (Z_lt_le_dec x hi); [|right; lia].
  exfalso. apply (app_not_shadow x); [apply H; lia | exact Hx].
Qed.

Lemma addressable_app : forall m p n, addressable m p n -> app_ivl p (p + n).
Proof.
  intros m p n (_ & _ & _ & H) a Ha. destruct (H (a - p) ltac:(lia)) as [Ha' _].
  replace a with (p + (a - p)) by lia. exact Ha'.
Qed.

Lemma addressable_sub : forall m p n k n', addressable m p n -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  addressable m (p + k) n'.
Proof.
  intros m p n k n' (H1 & H2 & H3 & H) Hk Hn' Hkn. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p + k + i) with (p + (k + i)) by lia. apply H. lia.
Qed.

Lemma addressable_kept : forall m m' p n, addressable m p n -> meta_kept m m' -> addressable m' p n.
Proof.
  intros m m' p n (H1 & H2 & H3 & H) MK. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite MK; [exact Hb|]. apply shadow_of_app. exact Ha.
Qed.

Lemma shadow_rw_kept : forall m m', shadow_rw m -> meta_kept m m' -> wmono rsegs m m' -> shadow_rw m'.
Proof.
  intros m m' H MK WM a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM, Hw|].
  exists b. rewrite MK by exact Ha. exact Hb.
Qed.

Fixpoint all_app (W : list ivl) : Prop :=
  match W with [] => True | (lo, hi) :: W' => app_ivl lo hi /\ all_app W' end.

Lemma munch_meta : forall W m m', munch W m m' -> all_app W -> meta_kept m m'.
Proof.
  intros W m m' MU AW a Ha. unfold mrd. rewrite (MU (wa a)); [reflexivity|].
  destruct (in_shadow_range a Ha) as [R1 R2]. rewrite wa_unsigned by lia.
  clear MU. induction W as [|[lo hi] W IH]; cbn [outside all_app] in *; [exact I|].
  destruct AW as [A1 A2]. split; [pose proof (app_ivl_meta lo hi a A1 Ha); lia | exact (IH A2)].
Qed.

Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n ->
  disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros a n a' n' H Ha Hn; [exact I|].
  destruct H as [H1 H2]. split; [lia | eapply IH; eauto].
Qed.

Lemma asan_cells_kept : forall W m m', asan_cells m -> munch W m m' -> disjoint_from W RT_LO (RT_HI - RT_LO) ->
  asan_cells m'.
Proof.
  intros W m m' AC MU D. unfold asan_cells, RT_LO, RT_HI in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply bytes_at_transport; [eassumption | exact MU | ]);
    (eapply disjoint_from_sub; [exact D | | ]); rewrite ?length_le8, ?length_le4; cbn [length];
    unfold CELL_K, UAR, INITED, REPLACE, CANPOISON, HIEND, MIDBEG, MIDEND, REAL_MEMCPY, REAL_MEMSET,
      GOT_CELL_K, GOT_UAR, GOT_REPLACE, GOT_HIEND, GOT_MIDBEG, GOT_MIDEND, GOT_REAL_MEMSET; lia.
Qed.

Lemma ro_c8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. split; [split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma sbyte_range : forall b : byte, -128 <= bv_signed b < 128.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128.
  Z.div_mod_to_equations. lia.
Qed.

Lemma byte_s0 : forall b : byte, bv_signed b = 0 -> b = Z_to_bv 8 0.
Proof.
  intros b H. apply bv_eq. pose proof (bv_unsigned_in_range 8 b) as R.
  change (bv_unsigned (Z_to_bv 8 0)) with 0.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128 in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  destruct (z mod 2^64 <? 2^63) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
    Z.div_mod_to_equations; lia.
Qed.

Lemma sxb_unsigned : forall b : byte, 0 <= bv_signed b -> bv_unsigned (sxb b) = bv_signed b.
Proof. intros b H. unfold sxb. apply unsigned_lit. pose proof (sbyte_range b). lia. Qed.

Lemma lts_sxb : forall x (b : byte), -2^63 <= x < 2^63 -> bv_lts (Z_to_bv 64 x) (sxb b) = (x <? bv_signed b).
Proof.
  intros x b Hx. unfold bv_lts, sxb. pose proof (sbyte_range b).
  rewrite !signed_lit by lia. reflexivity.
Qed.

Lemma land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma meta_byte : forall m p n, addressable m p n -> 1 <= n <= 8 ->
  exists b, ro_cells rsegs m (Z.shiftr p 3 + ASAN_K) [C1 b] /\
    (bv_signed b = 0 \/ p mod 8 + n - 1 < bv_signed b <= 7) /\ in_shadow (Z.shiftr p 3 + ASAN_K).
Proof.
  intros m p n AD Hn. pose proof AD as (H1 & H2 & H3 & H).
  destruct (H 0 ltac:(lia)) as (A0 & b & Rb & _). rewrite Z.add_0_r in A0, Rb.
  assert (SH : Z.shiftr p 3 + ASAN_K = shadow_addr p)
    by (unfold shadow_addr; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (G : forall i, 0 <= i < n -> p mod 8 + i <= 7 -> shadow_ok (p + i) (bv_signed b)).
  { intros i Hi Hr. destruct (H i Hi) as (_ & b' & Rb' & OK).
    replace (shadow_addr (p + i)) with (shadow_addr p) in Rb'.
    - rewrite Rb in Rb'. injection Rb' as <-. exact OK.
    - unfold shadow_addr. f_equal. Z.div_mod_to_equations. lia. }
  pose proof (shadow_of_app p A0) as IS. rewrite <- SH in IS.
  pose proof (in_shadow_range _ IS) as IR.
  exists b. split; [|split; [|exact IS]].
  - split; [split; exact I|]. cbn [cells_bytes cbytes app].
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i]; [|cbn [length] in Hi; lia].
    cbn [nth_error Z.of_nat]. rewrite Z.add_0_r, SH. exact Rb.
  - pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as PM.
    destruct (Z_le_gt_dec (p mod 8 + n - 1) 7) as [Hle|Hgt].
    + pose proof (G (n - 1) ltac:(lia) ltac:(lia)) as OK. unfold shadow_ok in OK.
      replace ((p + (n - 1)) mod 8) with (p mod 8 + n - 1) in OK by (Z.div_mod_to_equations; lia). lia.
    + pose proof (G (7 - p mod 8) ltac:(lia) ltac:(lia)) as OK. unfold shadow_ok in OK.
      replace ((p + (7 - p mod 8)) mod 8) with 7 in OK by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma meta8 : forall m p, addressable m p 8 ->
  ro_cells rsegs m (Z.shiftr p 3 + ASAN_K) [C1 (Z_to_bv 8 0)] /\ in_shadow (Z.shiftr p 3 + ASAN_K).
Proof.
  intros m p AD. destruct (meta_byte m p 8 AD ltac:(lia)) as (b & R & K & I).
  pose proof (Z.mod_pos_bound p 8 ltac:(lia)).
  assert (K0 : bv_signed b = 0) by lia. rewrite (byte_s0 b K0) in R. split; assumption.
Qed.

Lemma addressable_prefix : forall m p n n', addressable m p n -> 0 <= n' <= n -> addressable m p n'.
Proof.
  intros m p n n' (H1 & H2 & H3 & H) Hn. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. apply H. lia.
Qed.

Lemma app_ivl_sub : forall lo hi lo' hi', app_ivl lo hi -> lo <= lo' -> hi' <= hi -> app_ivl lo' hi'.
Proof. intros lo hi lo' hi' H H1 H2 a Ha. apply H. lia. Qed.

Lemma bv_ltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma bv_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma sx32_nz : forall f, 0 < f < 2^32 -> negb (bv_eqb (sx32 (Z_to_bv 64 f)) (Z_to_bv 64 0)) = true.
Proof.
  intros f Hf. unfold bv_eqb, sx32. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2^64). change (bv_half_modulus 32) with (2^31).
  change (bv_modulus 32) with (2^32). apply negb_true_iff, Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma wr_at_sub : forall m a n k n', wr_at rsegs m a n -> 0 <= k -> 0 <= n' -> k + n' <= n -> wr_at rsegs m (a + k) n'.
Proof.
  intros m a n k n' (Ha & Hn & H) Hk Hn' Hkn. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Lemma wr_at_shrink : forall m a n n', wr_at rsegs m a n -> 0 <= n' <= n -> wr_at rsegs m a n'.
Proof. intros m a n n' (Ha & Hn & H) Hn'. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.
