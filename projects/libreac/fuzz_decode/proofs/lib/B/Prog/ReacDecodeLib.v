From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c.
Import ListNotations.
Open Scope Z_scope.

Lemma eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma lts0_lit : forall x, -2^63 <= x < 2^63 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 x) = (0 <? x).
Proof.
  intros x Hx. rewrite bv_lts_zero_l. rewrite unsigned_lit_wrap.
  destruct (Z_lt_le_dec x 0) as [N|P].
  - rewrite <- (Z.mod_add x 1) by lia. rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec 0 x); destruct (Z.ltb_spec (x + 1 * 2^64) (2^63)); cbn [andb]; try reflexivity; lia.
  - rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec 0 x); destruct (Z.ltb_spec x (2^63)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit_wrap. apply (f_equal (Z_to_bv 64)).
  unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity. replace (bv_modulus 32) with (2^32) by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma firstn1_skipn : forall (bs : list byte) i d, (i < length bs)%nat -> firstn 1 (skipn i bs) = [nth i bs d].
Proof.
  induction bs as [|b bs IH]; intros i d H; cbn in H; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma mrd_write1 : forall m a b x, 0 <= a -> a + 1 <= 2^64 -> 0 <= x < 2^64 ->
  mrd rsegs (write_to_mem m (Z_to_bv 64 a) [b]) (Z_to_bv 64 x) = if x =? a then Some b else mrd rsegs m (Z_to_bv 64 x).
Proof.
  intros m a b x Ha Ha1 Hx. unfold mrd. change (Z_to_bv 64 a) with (wa a).
  rewrite write_to_mem_spec by (cbn; lia). rewrite unsigned_lit by lia.
  destruct (Z.eqb_spec x a) as [E|E].
  - subst x. destruct (Z.leb_spec a a); destruct (Z.ltb_spec a (a + Z.of_nat (length [b]))); cbn [andb];
      try (cbn in *; lia).
    rewrite Z.sub_diag. reflexivity.
  - destruct (Z.leb_spec a x); destruct (Z.ltb_spec x (a + Z.of_nat (length [b]))); cbn [andb];
      try reflexivity; cbn in *; lia.
Qed.

Lemma nth_error_mapseq : forall (f : Z -> byte) n i s, (i < n)%nat ->
  nth_error (map f (map Z.of_nat (seq s n))) i = Some (f (Z.of_nat (s + i))).
Proof.
  intros f n. induction n as [|n IH]; intros i s H; [lia|].
  cbn [seq map]. destruct i as [|i].
  - cbn. rewrite Nat.add_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma length_mapseq : forall (f : Z -> byte) n s, length (map f (map Z.of_nat (seq s n))) = n.
Proof. intros. rewrite !length_map, length_seq. reflexivity. Qed.

Lemma bytes_at_of_fun : forall m A (f : Z -> byte) n,
  0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat n -> mrd rsegs m (Z_to_bv 64 (A + i)) = Some (f i)) ->
  bytes_at rsegs m A (map f (map Z.of_nat (seq 0 n))).
Proof.
  intros m A f n HA Hn H. split; [lia|]. rewrite length_mapseq. split; [lia|].
  intros i Hi. rewrite nth_error_mapseq by lia. cbn [Nat.add].
  apply H. lia.
Qed.

Lemma munch_extend : forall (m m1 : word -> option byte) a b c d,
  munch [(a, b)] m m1 -> munch [(a, b); (c, d)] m m1.
Proof.
  intros m m1 a b c d H. eapply munch_weaken; [|exact H].
  intros x Hx. cbn [outside] in *. tauto.
Qed.

Lemma munch_wider : forall (m m1 : word -> option byte) a b c d,
  c <= a -> b <= d -> munch [(a, b)] m m1 -> munch [(c, d)] m m1.
Proof.
  intros m m1 a b c d H1 H2 H. eapply munch_weaken; [|exact H].
  intros x Hx. cbn [outside] in *. split; [lia | exact I].
Qed.

Lemma munch_wider2 : forall (m m1 : word -> option byte) a b c d e f,
  c <= a -> b <= d -> munch [(a, b); (e, f)] m m1 -> munch [(c, d); (e, f)] m m1.
Proof.
  intros m m1 a b c d e f H1 H2 H. eapply munch_weaken; [|exact H].
  intros x Hx. cbn [outside] in *. destruct Hx as (Hx1 & Hx2 & _). split; [lia | split; [exact Hx2 | exact I]].
Qed.

Lemma inspect_counter_range : forall bs, 0 <= inspect_counter bs < 2^16.
Proof.
  intros bs. unfold inspect_counter, inspect_byte.
  pose proof (bv_unsigned_in_range 8 (nth 14 bs (Z_to_bv 8 0))) as H1.
  pose proof (bv_unsigned_in_range 8 (nth 15 bs (Z_to_bv 8 0))) as H2.
  unfold bv_modulus in H1, H2. change (2 ^ Z.of_N 8) with 256 in H1, H2. lia.
Qed.

Lemma inspect_valid_bit : forall len bs,
  Z.shiftr (bv_unsigned (Z_to_bv 64 (inspect_result len bs))) 32 = if inspect_wf len bs then 1 else 0.
Proof.
  intros len bs. pose proof (inspect_counter_range bs) as Hc. unfold inspect_result.
  destruct (inspect_wf len bs).
  - rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace (2^32 + inspect_counter bs) with (inspect_counter bs + 1 * 2^32) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
  - reflexivity.
Qed.

Lemma braid_div : forall ch s k ns, 0 <= ch -> 0 <= s < ns -> 0 <= k < 3 ->
  (3 * (ch * ns + s) + k) / 3 = ch * ns + s /\ (3 * (ch * ns + s) + k) mod 3 = k /\
  (ch * ns + s) mod ns = s /\ (ch * ns + s) / ns = ch.
Proof.
  intros ch s k ns Hch Hs Hk.
  replace (3 * (ch * ns + s) + k) with (k + (ch * ns + s) * 3) by ring.
  replace (ch * ns + s) with (s + ch * ns) by ring.
  rewrite Z.div_add, Z.mod_add by lia. rewrite (Z.div_small k 3), (Z.mod_small k 3) by lia.
  rewrite Z.div_add, Z.mod_add by lia. rewrite Z.div_small, Z.mod_small by lia. lia.
Qed.

Lemma wv : forall (x : word) v, bv_unsigned x = v -> x = Z_to_bv 64 v.
Proof. intros x v H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma zx32_lit : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma sextw_zx32 : forall z, -2^31 <= z < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (zx32 (Z_to_bv 64 z)) + 0)) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zx32. rewrite !unsigned_lit_wrap. apply (f_equal (Z_to_bv 64)).
  unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity. replace (bv_modulus 32) with (2^32) by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma land_m2 : forall c, 0 <= c < 2^64 -> Z.land c 18446744073709551614 = 2 * (c / 2).
Proof.
  intros c Hc.
  replace 18446744073709551614 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 1))) by reflexivity.
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. cbn. lia.
Qed.

Lemma land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. pose proof (Z.land_ones x 1 ltac:(lia)) as H. cbn in H. exact H. Qed.

Lemma swrap32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity. replace (bv_modulus 32) with (2^32) by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma lts_sm : forall (x : Z) (k : byte), 0 <= x < 2^63 -> bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

Lemma app_win : forall s d x, 0 < d <= 2^32 -> app_mem (s - d) -> app_mem (s - 1) -> s - d <= x < s -> app_mem x.
Proof. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros s d x Hd H1 H2 Hx. lia. Qed.

Lemma shadow_not_app : forall a, app_mem a -> ~ app_mem (a / 8 + ASAN_K).
Proof.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros a Ha Hs. Z.div_mod_to_equations. lia.
Qed.

Lemma in_shadow_not_app : forall a, in_shadow a -> ~ app_mem a.
Proof. unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. lia. Qed.

Lemma shadow_range : forall a, app_mem a -> 0 <= a / 8 + ASAN_K < 2^64.
Proof.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros a Ha. Z.div_mod_to_equations. lia.
Qed.

Lemma mrd_munch : forall W m m' a, munch W m m' -> 0 <= a < 2^64 -> outside W a ->
  mrd rsegs m' (wa a) = mrd rsegs m (wa a).
Proof.
  intros W m m' a MU Ha Ho. unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by exact Ha. exact Ho.
Qed.

Lemma shadow_rw_munch : forall W m m', shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> outside W a) -> shadow_rw m'.
Proof.
  intros W m m' SR MU WM D a Ha. destruct (SR a Ha) as [Hw (b & Hb)].
  assert (R : 0 <= a < 2^64)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha; lia).
  split; [apply WM, Hw|]. exists b. rewrite (mrd_munch W m m' a MU R (D a Ha)). exact Hb.
Qed.

Lemma addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W ((p + i) / 8 + ASAN_K)) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & H1 & H2 & H) MU D.
  split; [exact H0 | split; [exact H1 | split; [exact H2 | ]]].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  unfold shadow_addr in *. rewrite (mrd_munch W m m' _ MU (shadow_range _ Ha) (D i Hi)). exact Hb.
Qed.

Lemma asan_cells_munch : forall m m' lo hi, asan_cells m -> munch [(lo, hi)] m m' ->
  MIDEND + 8 <= lo \/ hi <= GOT_CELL_K -> asan_cells m'.
Proof.
  unfold asan_cells, MIDEND, GOT_CELL_K.
  intros m m' lo hi (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17) MU D.
  unfold CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND, GOT_HIEND, MIDBEG,
    GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, REAL_MEMSET, GOT_REAL_MEMSET in *.
  repeat (match goal with |- _ /\ _ => split end);
    (eapply bytes_tp; [exact MU | | eassumption]); rewrite ?length_le8, ?length_le4; cbn [length]; lia.
Qed.

Lemma addr_one : forall m p n i, addressable m p n -> 0 <= i < n ->
  app_mem (p + i) /\ exists k, mrd rsegs m (wa ((p + i) / 8 + ASAN_K)) = Some k /\
    (bv_signed k = 0 \/ (p + i) mod 8 < bv_signed k).
Proof.
  intros m p n i (H0 & H1 & H2 & H) Hi. destruct (H i Hi) as (Ha & k & Hk & Hok).
  split; [exact Ha|]. exists k. unfold shadow_addr in Hk. split; [exact Hk|].
  unfold shadow_ok in Hok. lia.
Qed.

Lemma addr_four : forall m p n a, addressable m p n -> p <= a -> a + 4 <= p + n ->
  exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ a mod 8 + 3 < bv_signed k).
Proof.
  intros m p n a (H0 & H1 & H2 & H) Ha Hn.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Mb.
  destruct (Z_le_gt_dec (a mod 8) 4) as [L|L].
  - destruct (H (a + 3 - p) ltac:(lia)) as (Hap & k & Hk & Hok).
    replace (p + (a + 3 - p)) with (a + 3) in Hk, Hok by lia.
    assert (E1 : (a + 3) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
    assert (E2 : (a + 3) mod 8 = a mod 8 + 3) by (Z.div_mod_to_equations; lia).
    unfold shadow_addr in Hk. rewrite E1 in Hk. unfold shadow_ok in Hok. rewrite E2 in Hok.
    exists k. split; [exact Hk | lia].
  - destruct (H (a + (7 - a mod 8) - p) ltac:(lia)) as (Hap & k & Hk & Hok).
    replace (p + (a + (7 - a mod 8) - p)) with (a + (7 - a mod 8)) in Hk, Hok by lia.
    assert (E1 : (a + (7 - a mod 8)) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
    assert (E2 : (a + (7 - a mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
    unfold shadow_addr in Hk. rewrite E1 in Hk. unfold shadow_ok in Hok. rewrite E2 in Hok.
    exists k. split; [exact Hk | lia].
Qed.

Ltac brq BR :=
  rewrite ?eqb_lit, ?ltu_lit by lia;
  lazymatch goal with
  | |- context [if negb (Z.eqb ?a ?b) then _ else _] => destruct (Z.eqb_spec a b) as [BR|BR]
  | |- context [if Z.eqb ?a ?b then _ else _] => destruct (Z.eqb_spec a b) as [BR|BR]
  | |- context [if negb (Z.ltb ?a ?b) then _ else _] => destruct (Z.ltb_spec a b) as [BR|BR]
  | |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb_spec a b) as [BR|BR]
  end; cbn [negb].

Lemma land3_0 : forall x, 0 <= x -> x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x Hx H. replace 3 with (Z.ones 2) by reflexivity. rewrite Z.land_ones by lia. exact H. Qed.

Lemma lxor_m1 : forall x, 0 <= x < 2^64 -> Z.lxor x (bv_wrap 64 (-1)) = 2^64 - 1 - x.
Proof.
  intros x Hx. replace (bv_wrap 64 (-1)) with 18446744073709551615 by reflexivity.
  rewrite zb_lxor_ones by lia. lia.
Qed.

Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.

Ltac nrm := usub; rewrite ?Z.shiftl_mul_pow2 by lia; zb_fold_lits;
  repeat match goal with |- context [bv_swrap 32 ?z] => rewrite (swrap32_id z) by lia end.

Ltac st := step; nrm.

Ltac cnd b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts; usub; fold_lit_ux; solve_cond_rec]
  end.

Lemma eqb_litw : forall x (y : word), 0 <= x < 2^64 -> bv_eqb (Z_to_bv 64 x) y = (x =? bv_unsigned y).
Proof. intros x y Hx. unfold bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma eqb_ww : forall x y : word, bv_eqb x y = (bv_unsigned x =? bv_unsigned y).
Proof. reflexivity. Qed.

Lemma slli_srli32 : forall z, 0 <= z < 2^31 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 32))) 32) = Z_to_bv 64 z.
Proof.
  intros z Hz. rewrite (unsigned_lit z) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma land_m8 : forall c, 0 <= c < 2^64 -> Z.land c 18446744073709551608 = 8 * (c / 8).
Proof.
  intros c Hc.
  replace 18446744073709551608 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 3))) by reflexivity.
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. cbn. lia.
Qed.

Lemma land_2m2 : forall x, 0 <= x < 2^31 -> Z.land x 2147483646 = x - x mod 2.
Proof.
  intros x Hx.
  replace 2147483646 with (Z.land (Z.ones 31) (Z.lnot (Z.ones 1))) by reflexivity.
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. cbn. Z.div_mod_to_equations. lia.
Qed.

Lemma geom_bounds : forall a b, 1 <= a -> 1 <= b -> a * b <= 480 -> a <= 480 /\ b <= 480.
Proof. intros. nia. Qed.

Lemma row_bounds : forall s ns nch, 0 <= s < ns -> 0 <= nch -> 0 <= s * nch /\ s * nch <= (ns - 1) * nch.
Proof. intros. split; nia. Qed.

Lemma prod_bound62 : forall a b, 0 <= a < 2^31 -> 0 <= b < 2^31 -> 0 <= a * b < 2^62.
Proof. intros. nia. Qed.

Ltac ufin := first [ reflexivity | (apply unsigned_lit; lia) | (usub; rewrite ?lxor_m1, ?zb_lxor_ones by lia; usub; lia) ].
