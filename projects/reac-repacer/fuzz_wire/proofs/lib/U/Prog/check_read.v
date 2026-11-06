(* check_read walk, fuzz_wire ubsan 6e91fe0b5555 0x13300..0x13550 (fuzz_wire.c:212-251); new.
   rp_slot_read is the named Section hypothesis H_rp_slot_read (lib/U/Prog/rp_slot_read_c.v, `jal` at
   0x133bc). The UBSan build fills v[] inline (0x13348..0x13358, no memset call) and inlines w_width (0x1335c..0x13394)
   and w_get (the loop body 0x13420..0x134d0). Its UBSan traps, each an `unimp`, are refuted: c + 16 / c + 17 overflow
   (0x1339c, 0x13524: c + len <= 2^64 with len >= 50), s * nch and s * nch + (slot & ~1) overflow int (0x1342c, 0x1343c:
   s <= 11, nch <= 40), the frame pointer c + 3 * (..) + 50 and its walk overflow (0x13450, 0x13470: inside c's len
   bytes), be + at + k overflows (0x13498..0x134a0: inside the frame below sp). Structure as the plain walk: ww_loopU,
   cr_b16 / cr_zero, cr_tail, cr_loop (12 samples), cr_exit.
   land_hi is ported from libreac/fuzz_decode lib/Prog/check_braid.v:9-27 (recipes 25e3d17bdb5, released). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import FrameBytes reac_frame_clean_len_c
  rp_frame_channels_c rp_slot_width_c rp_slot_read_c check_read_c.
Import ListNotations.
Open Scope Z_scope.

Lemma bveqb_lit : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. Z.div_mod_to_equations. lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at, wr_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] (H1 & H2 & H3)].
    rewrite (cells_bytes_length cs1 W1) in B2.
    split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]).
    + intros i Hi. apply H3. lia.
    + intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply H3. lia.
  - intros [[[W1 B1] (H1 & H2 & H3)] [[W2 B2] (K1 & K2 & K3)]].
    rewrite <- (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption | split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))) as [L|L]; [apply H3; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply K3. lia.
Qed.

Lemma rdz : forall m a bs k, bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof. intros m a bs k H Hk. pose proof (rd1 m a bs (Z.to_nat k) H ltac:(lia)) as R. rewrite Z2Nat.id in R by lia. exact R. Qed.

(* Ported from libreac/fuzz_decode lib/Prog/check_braid.v:9-27 (recipes 25e3d17bdb5, released). *)
Lemma land_hi : forall x k, 0 <= x < 2^64 -> 0 <= k <= 64 -> Z.land x (2^64 - 2^k) = 2^k * (x / 2^k).
Proof.
  intros x k Hx Hk.
  assert (E : 2^64 - 2^k = Z.shiftl (Z.ones (64 - k)) k).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv. unfold Z.pred.
    rewrite Z.mul_add_distr_r, <- Z.pow_add_r by lia. replace (64 - k + k) with 64 by lia. lia. }
  rewrite E, (Z.mul_comm (2^k)), <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i k).
  - rewrite (Z.testbit_neg_r (Z.ones (64 - k)) (i - k)), (Z.testbit_neg_r (Z.shiftr x k) (i - k)) by lia.
    apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - k + k) with i by lia.
    destruct (Z.ltb_spec i 64).
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
      destruct (Z.eq_dec x 0) as [->|Hnz]; [symmetry; apply Z.bits_0|].
      symmetry. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma lor_disj : forall a b k, 0 <= k -> 0 <= a < 2^k -> 0 <= b -> Z.lor a (b * 2^k) = a + b * 2^k.
Proof.
  intros a b k Hk Ha Hb.
  assert (L : Z.land a (b * 2^k) = 0).
  { rewrite <- Z.shiftl_mul_pow2 by lia. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec i k).
    - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - replace (Z.testbit a i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec a 0) as [->|Hnz]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

(* fuzz.h:93-104, the braid read check_read compares v[s] with (inlined into check_read's loop):
     static inline int32_t w_get(const uint8_t *f, int s, int ch, int nch)
     {
       const uint8_t *g = f + w_group(s, ch, nch);
       uint8_t be[6];
       for (int w = 0; w < 3; w++) {
         be[2 * w] = g[2 * w + 1];
         be[2 * w + 1] = g[2 * w];
       }
       int at = (ch & 1) ? 3 : 0;
       uint32_t u = (uint32_t)be[at] << 16 | (uint32_t)be[at + 1] << 8 | be[at + 2];
       return u >= 0x800000u ? (int32_t)u - 0x1000000 : (int32_t)u;
     }
   w_group(s, ch, nch) = W_AUDIO + (s * nch + (ch & ~1)) * 3 (fuzz.h:70-73). samp24 hi mid lo is w_get's value from
   the three bytes be[at], be[at + 1], be[at + 2]; wsamp is the 64-bit word the compiled code builds from them. *)
Definition wsamp (hi mid lo : byte) : word :=
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned
    (Z_to_bv 64 (Z.land (bv_unsigned (sxb hi)) 255))) 16))) (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (zxb lo))
    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb mid)) 8)))))))))
    (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sxb hi)) 18446744073692774400)))).

Definition samp24 (hi mid lo : byte) : Z :=
  let x := bv_unsigned lo + 256 * bv_unsigned mid + 65536 * bv_unsigned hi in if x <? 2^23 then x else x - 2^24.

Lemma sxb_unsigned : forall b : byte,
  bv_unsigned (sxb b) = if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b + 2^64 - 256.
Proof.
  intros b. pose proof (byte_range b) as R. unfold sxb. rewrite unsigned_lit_wrap.
  change (bv_signed b) with (bv_swrap 8 (bv_unsigned b)). unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  destruct (Z.ltb_spec (bv_unsigned b) 128).
  - rewrite (Z.mod_small (bv_unsigned b + 128) 256) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((bv_unsigned b + 128) mod 256) with (bv_unsigned b - 128)
      by (apply Z.mod_unique with (q := 1); lia).
    replace (bv_unsigned b - 128 - 128) with ((bv_unsigned b + 2^64 - 256) + (-1) * 2^64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma wsamp_eq : forall hi mid lo, wsamp hi mid lo = Z_to_bv 64 (samp24 hi mid lo).
Proof.
  intros hi mid lo. pose proof (byte_range hi) as Rh. pose proof (byte_range mid) as Rm. pose proof (byte_range lo) as Rl.
  unfold wsamp, samp24. cbv zeta. unfold zxb. rewrite (unsigned_lit (bv_unsigned mid)), (unsigned_lit (bv_unsigned lo)) by lia.
  rewrite sxb_unsigned.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  replace 18446744073692774400 with (2^64 - 2^24) by reflexivity.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (bv_unsigned mid * 2 ^ 8)) by lia.
  rewrite (lor_disj (bv_unsigned lo) (bv_unsigned mid) 8) by lia.
  rewrite (unsigned_lit (bv_unsigned lo + bv_unsigned mid * 2 ^ 8)) by lia.
  destruct (Z.ltb_spec (bv_unsigned hi) 128) as [H|H].
  - rewrite (Z.mod_small (bv_unsigned hi) (2 ^ 8)) by lia.
    rewrite (unsigned_lit (bv_unsigned hi)) by lia.
    rewrite (unsigned_lit (bv_unsigned hi * 2 ^ 16)) by lia.
    rewrite (Z.lor_comm (bv_unsigned hi * 2 ^ 16)), (lor_disj _ (bv_unsigned hi) 16) by lia.
    rewrite (unsigned_lit (bv_unsigned lo + bv_unsigned mid * 2 ^ 8 + bv_unsigned hi * 2 ^ 16)) by lia.
    rewrite land_hi by lia. rewrite Z.div_small by lia. rewrite Z.mul_0_r. rewrite (unsigned_lit 0) by lia.
    rewrite Z.lor_0_r.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. f_equal. lia.
  - replace ((bv_unsigned hi + 2 ^ 64 - 256) mod 2 ^ 8) with (bv_unsigned hi)
      by (apply Z.mod_unique with (q := 2^56 - 1); lia).
    rewrite (unsigned_lit (bv_unsigned hi)) by lia.
    rewrite (unsigned_lit (bv_unsigned hi * 2 ^ 16)) by lia.
    rewrite (Z.lor_comm (bv_unsigned hi * 2 ^ 16)), (lor_disj _ (bv_unsigned hi) 16) by lia.
    rewrite (unsigned_lit (bv_unsigned lo + bv_unsigned mid * 2 ^ 8 + bv_unsigned hi * 2 ^ 16)) by lia.
    rewrite land_hi by lia.
    replace ((bv_unsigned hi + 2 ^ 64 - 256) / 2 ^ 24) with (2^40 - 1)
      by (apply Z.div_unique with (r := bv_unsigned hi + 2^24 - 256); lia).
    rewrite unsigned_lit by lia.
    replace (2 ^ 24 * (2 ^ 40 - 1)) with ((2^40 - 1) * 2^24) by ring.
    rewrite (lor_disj _ (2^40 - 1) 24) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. apply Z_to_bv_eqm. Z.div_mod_to_equations. lia.
Qed.

Lemma rps : forall bs nch slot s p0 p1 p2,
  Z.to_nat (50 + braid_pos s slot nch 0) = p0 -> Z.to_nat (50 + braid_pos s slot nch 1) = p1 ->
  Z.to_nat (50 + braid_pos s slot nch 2) = p2 ->
  rp_sample bs nch slot s = samp24 (nth p2 bs (Z_to_bv 8 0)) (nth p1 bs (Z_to_bv 8 0)) (nth p0 bs (Z_to_bv 8 0)).
Proof. intros. unfold rp_sample, samp24. subst. reflexivity. Qed.

Lemma samp24_range : forall hi mid lo, -2^23 <= samp24 hi mid lo < 2^23.
Proof.
  intros. pose proof (byte_range hi). pose proof (byte_range mid). pose proof (byte_range lo).
  unfold samp24. cbv zeta. destruct (Z.ltb_spec (bv_unsigned lo + 256 * bv_unsigned mid + 65536 * bv_unsigned hi) (2^23)); lia.
Qed.

Lemma sx32_lit : forall y, -2^31 <= y < 2^31 -> sx32 (Z_to_bv 64 y) = Z_to_bv 64 y.
Proof.
  intros y Hy. unfold sx32. rewrite unsigned_lit_wrap. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.

Definition le4s (f : Z -> Z) : list byte := flat_map (fun s => le4 (Z_to_bv 64 (f (Z.of_nat s)))) (seq 0 12).

Lemma flat4_nth : forall (g : nat -> list byte), (forall x, length (g x) = 4%nat) ->
  forall n a k, (k < n)%nat -> firstn 4 (skipn (4 * k) (flat_map g (seq a n))) = g (a + k)%nat.
Proof.
  intros g Hg. induction n as [|n IH]; intros a k Hk; [lia|].
  cbn [seq flat_map]. destruct k as [|k].
  - rewrite Nat.mul_0_r, Nat.add_0_r, skipn_O. rewrite firstn_app, Hg, Nat.sub_diag, firstn_all2 by (rewrite Hg; lia).
    cbn [firstn]. apply app_nil_r.
  - replace (4 * S k)%nat with (length (g a) + 4 * k)%nat by (rewrite Hg; lia).
    rewrite skipn_app, skipn_all2 by lia. cbn [app].
    replace (length (g a) + 4 * k - length (g a))%nat with (4 * k)%nat by lia.
    rewrite IH by lia. f_equal. lia.
Qed.

Lemma le4s_read : forall m A f i, bytes_at rsegs m A (le4s f) -> 0 <= i < 12 ->
  ov_read_bytes rsegs m (wa (A + 4 * i)) 4 = Some (le4 (Z_to_bv 64 (f i))).
Proof.
  intros m A f i H Hi.
  assert (L : length (le4s f) = 48%nat) by (unfold le4s; cbn [seq flat_map]; rewrite !length_app, !length_le4; reflexivity).
  rewrite (bytes_at_read rsegs m A (le4s f) (4 * i) 4 H) by lia. f_equal.
  replace (Z.to_nat (4 * i)) with (4 * Z.to_nat i)%nat by lia.
  unfold le4s. rewrite (flat4_nth (fun s => le4 (Z_to_bv 64 (f (Z.of_nat s))))) by (first [intros; apply length_le4 | lia]).
  cbn [Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma cells_rd1 : forall m A cs k b, rw_cells rsegs m A cs -> cell_at cs k = Some (C1 b) ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat k)) 1 = Some [b].
Proof. intros m A cs k b H E. exact (rw_cells_read rsegs m A cs k (C1 b) H E). Qed.

(* fuzz.h:55-63, the frame law check_read compares the reader with (inlined into check_read):
     static inline int w_width(long len)
     {
       for (int nch = 2; nch <= W_MAX_CH; nch += 2) {
         long clean = W_OVERHEAD + (long)nch * W_PER_CH;
         if (len == clean || len == clean + W_RESIDUE)
           return nch;
       }
       return -1;
     }
   W_OVERHEAD = 52, W_PER_CH = 36, W_MAX_CH = 40, W_RESIDUE = 2 (fuzz.h:26-30). ww_go walks the same table. *)
Fixpoint ww_go (fuel : nat) (nch len : Z) : Z :=
  match fuel with
  | O => -1
  | S f => if (len =? 52 + nch * 36) || (len =? 52 + nch * 36 + 2) then nch else ww_go f (nch + 2) len
  end.



Lemma sw32 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma bvltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.



Definition w_width_model (len : Z) : Z := ww_go 20 2 len.



Ltac sbstep := step; rewrite ?le1_zxb; mem_after_store_opt.

Lemma rw_cells_wr : forall m A cs n, rw_cells rsegs m A cs -> 0 <= n <= Z.of_nat (cells_size cs) -> wr_at rsegs m A n.
Proof. intros m A cs n [_ (W1 & W2 & W3)] Hn. split; [lia|]. split; [lia|]. intros j Hj. apply W3. lia. Qed.

Lemma signed_mod2 : forall w : word, bv_signed w mod 2 = bv_unsigned w mod 2.
Proof.
  intros w. pose proof (u64_range w). change (bv_signed w) with (bv_swrap 64 (bv_unsigned w)).
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
  Z.div_mod_to_equations. lia.
Qed.

Lemma signed_nonneg : forall w : word, 0 <= bv_signed w -> bv_unsigned w = bv_signed w.
Proof.
  intros w H. pose proof (u64_range w). change (bv_signed w) with (bv_swrap 64 (bv_unsigned w)) in *.
  unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 64) with (2^63) in *. change (bv_modulus 64) with (2^64) in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma at_bits : forall w : word,
  Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 63))) 63))) 3
  = 3 * (bv_signed w mod 2).
Proof.
  intros w. pose proof (u64_range w). rewrite signed_mod2.
  replace (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 63)) with (Z_to_bv 64 ((bv_unsigned w mod 2) * 2^63)).
  2:{ apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. Z.div_mod_to_equations. lia. }
  assert (P : bv_unsigned w mod 2 = 0 \/ bv_unsigned w mod 2 = 1) by (Z.div_mod_to_equations; lia).
  destruct P as [P|P]; rewrite P; vm_compute; reflexivity.
Qed.

Lemma land_m2 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551614 = 2 * (x / 2).
Proof. intros x Hx. exact (land_hi x 1 Hx ltac:(lia)). Qed.

Definition ww_check (n : nat) : bool :=
  forallb (fun len => let w := w_width_model len in
    (w =? rp_frame_channels_model len) &&
    ((w =? -1) || ((2 <=? w) && (w <=? 40) && (w mod 2 =? 0) && ((len =? 52 + 36 * w) || (len =? 54 + 36 * w)))))
    (map Z.of_nat (seq 0 n)).

Lemma ww_check_ok : ww_check 1601 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ww_facts : forall len, 0 <= len <= 1600 ->
  w_width_model len = rp_frame_channels_model len /\
  (w_width_model len = -1 \/
   (2 <= w_width_model len <= 40 /\ w_width_model len mod 2 = 0 /\
    (len = 52 + 36 * w_width_model len \/ len = 54 + 36 * w_width_model len))).
Proof.
  intros len H. pose proof ww_check_ok as C. unfold ww_check in C. rewrite forallb_forall in C.
  specialize (C len). cbv zeta in C.
  assert (I : In len (map Z.of_nat (seq 0 1601))) by (apply in_map_iff; exists (Z.to_nat len); split; [lia | apply in_seq; lia]).
  specialize (C I). apply andb_prop in C as [C1 C2]. apply Z.eqb_eq in C1. split; [exact C1|].
  apply orb_prop in C2 as [C2|C2]; [left; apply Z.eqb_eq; exact C2 | right].
  apply andb_prop in C2 as [C2 C5]. apply andb_prop in C2 as [C2 C4]. apply andb_prop in C2 as [C2 C3].
  apply Z.leb_le in C2, C3. apply Z.eqb_eq in C4. split; [lia|]. split; [exact C4|].
  apply orb_prop in C5 as [C5|C5]; apply Z.eqb_eq in C5; lia.
Qed.

Lemma width_facts : forall n bs slot, 0 <= n <= 1600 -> 0 <= rp_slot_width_model n bs slot ->
  2 <= rp_slot_width_model n bs slot <= 40 /\ rp_slot_width_model n bs slot mod 2 = 0 /\
  0 <= slot < rp_slot_width_model n bs slot /\ 52 + 36 * rp_slot_width_model n bs slot <= n /\
  rp_slot_width_model n bs slot = w_width_model n.
Proof.
  intros n bs slot Hn H. unfold rp_slot_width_model in *.
  rewrite (bv_swrap_small 64 n) in * by (change (bv_half_modulus 64) with (2^63); lia).
  destruct ((n <? 50) || negb (slot_byte bs 16 =? 0) || negb (slot_byte bs 17 =? 0)); [lia|]. cbv zeta in *.
  destruct (ww_facts n Hn) as [E [E1 | (E2 & E3 & E4)]]; rewrite <- E in *.
  - rewrite E1 in H |- *. cbn in H. lia.
  - destruct (Z.ltb_spec (w_width_model n) 0); [lia|].
    destruct (Z.ltb_spec slot 0); [cbn in H; lia|].
    destruct (Z.leb_spec (w_width_model n) slot); [cbn in H; lia|]. cbn [orb].
    split; [lia|]. split; [exact E3|]. split; [lia|]. split; [lia | reflexivity].
Qed.

Lemma rw_cells_CB : forall m A bs n, length bs = n -> bytes_at rsegs m A bs -> wr_at rsegs m A (Z.of_nat n) ->
  rw_cells rsegs m A [CB n bs].
Proof.
  intros m A bs n L B W. split; [split|].
  - cbn. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.

Lemma rp_slot_bytes_length : forall bs nch slot, length (rp_slot_bytes bs nch slot) = 48%nat.
Proof. intros. unfold rp_slot_bytes. cbn [seq flat_map]. rewrite !length_app, !length_le4. reflexivity. Qed.

Lemma srm_zero : forall n bs slot,
  n < 50 \/ slot_byte bs 16 <> 0 \/ slot_byte bs 17 <> 0 \/ slot < 0 \/
  rp_frame_channels_model (bv_swrap 64 n) < 0 \/ rp_frame_channels_model (bv_swrap 64 n) <= slot ->
  rp_slot_read_model n bs slot = 0.
Proof.
  intros n bs slot H. unfold rp_slot_read_model, rp_slot_width_model. cbv zeta.
  destruct (Z.ltb_spec n 50); [reflexivity|].
  destruct (Z.eqb_spec (slot_byte bs 16) 0); [|reflexivity].
  destruct (Z.eqb_spec (slot_byte bs 17) 0); [|reflexivity]. cbn [negb orb].
  destruct (Z.ltb_spec (rp_frame_channels_model (bv_swrap 64 n)) 0); [reflexivity|].
  destruct (Z.ltb_spec slot 0); [reflexivity|].
  destruct (Z.leb_spec (rp_frame_channels_model (bv_swrap 64 n)) slot); [reflexivity|]. cbn [orb].
  exfalso. lia.
Qed.

Lemma srm_one : forall n bs slot, 50 <= n -> slot_byte bs 16 = 0 -> slot_byte bs 17 = 0 ->
  0 <= slot < rp_frame_channels_model (bv_swrap 64 n) ->
  rp_slot_read_model n bs slot = 1 /\ rp_slot_width_model n bs slot = rp_frame_channels_model (bv_swrap 64 n).
Proof.
  intros n bs slot H1 H2 H3 H4. unfold rp_slot_read_model, rp_slot_width_model. cbv zeta.
  rewrite (proj2 (Z.ltb_ge n 50) H1), H2, H3. cbn [Z.eqb negb orb].
  rewrite !(proj2 (Z.ltb_ge (rp_frame_channels_model (bv_swrap 64 n)) 0)) by lia.
  rewrite (proj2 (Z.ltb_ge slot 0)) by lia.
  rewrite (proj2 (Z.leb_gt (rp_frame_channels_model (bv_swrap 64 n)) slot)) by lia. cbn [orb].
  split; [|reflexivity]. rewrite (proj2 (Z.ltb_ge (rp_frame_channels_model (bv_swrap 64 n)) 0)) by lia. reflexivity.
Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. change (bv_signed (Z_to_bv 64 z)) with (bv_swrap 64 (bv_unsigned (Z_to_bv 64 z))).
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2^63).
  change (bv_modulus 64) with (2^64). Z.div_mod_to_equations. lia.
Qed.



Lemma bveqb_u : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Ltac br_eq := first [rewrite bveqb_lit by lia | rewrite bveqb_u by lia];
  first [rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia]; cbn [negb]; cbv iota.

Section WWU.
Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (len : Z) (Q : machine_state -> Prop).
Hypothesis Hlen : 0 <= len <= 1600.

Local Notation WST pc x10 x14 x18 :=
  (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 2) (Z_to_bv 64 38) x14 x15 x16 x17 x18 x19 x20
           x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Lemma ww_loopU : forall j k, Z.of_nat j + k = 19 -> 0 <= k ->
  (forall x10 x14 n, ww_go (S j) (2 + 2 * k) len = n -> 2 <= n <= 40 -> evt rsegs Q (WST 0x13398 x10 x14 (Z_to_bv 64 n))) ->
  (forall x10 x14 x18, ww_go (S j) (2 + 2 * k) len = -1 -> evt rsegs Q (WST 0x1338c x10 x14 x18)) ->
  evt rsegs Q (WST 0x13374 (Z_to_bv 64 (2 * k)) (Z_to_bv 64 (126 + 72 * k - len)) (Z_to_bv 64 (2 + 2 * k))).
Proof.
  induction j as [|j IH]; intros k Hk H0 KF KN.
  all: step; rewrite bveqb_lit by lia.
  all: destruct (Z.eqb_spec (126 + 72 * k - len) 2) as [E1|E1]; cbv iota.
  1,3: eapply KF; [cbn [ww_go]; rewrite (proj2 (Z.eqb_eq len (52 + (2 + 2 * k) * 36))) by lia; reflexivity | lia].
  all: step; rewrite bveqb_lit by lia.
  all: destruct (Z.eqb_spec (126 + 72 * k - len) 0) as [E2|E2]; cbv iota.
  1,3: eapply KF; [cbn [ww_go]; rewrite (proj2 (Z.eqb_neq len (52 + (2 + 2 * k) * 36))) by lia;
                   rewrite (proj2 (Z.eqb_eq len (52 + (2 + 2 * k) * 36 + 2))) by lia; reflexivity | lia].
  all: do 4 step; rewrite bvltu_lit by lia.
  all: rewrite (unsigned_lit (2 + 2 * k)), sw32 by lia.
  - rewrite (proj2 (Z.ltb_lt 38 (2 * k + 2))) by lia. cbv iota.
    apply KN. cbn [ww_go]. rewrite (proj2 (Z.eqb_neq len _)), (proj2 (Z.eqb_neq len _)) by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge 38 (2 * k + 2))) by lia. cbv iota.
    replace (2 * k + 2) with (2 * (k + 1)) by lia.
    replace (126 + 72 * k - len + 72) with (126 + 72 * (k + 1) - len) by lia.
    replace (2 + 2 * k + 2) with (2 + 2 * (k + 1)) by lia.
    apply (IH (k + 1)); [lia | lia | |].
    + intros x10 x14 n E R. apply KF; [|exact R]. rewrite <- E. cbn [ww_go].
      rewrite (proj2 (Z.eqb_neq len _)), (proj2 (Z.eqb_neq len _)) by lia. cbn [orb].
      replace (2 + 2 * k + 2) with (2 + 2 * (k + 1)) by lia. reflexivity.
    + intros x10 x14 x18 E. apply KN. rewrite <- E. cbn [ww_go].
      rewrite (proj2 (Z.eqb_neq len _)), (proj2 (Z.eqb_neq len _)) by lia. cbn [orb].
      replace (2 + 2 * k + 2) with (2 + 2 * (k + 1)) by lia. reflexivity.
Qed.
End WWU.



Lemma lxor_ones : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 2^64 - 1 - x.
Proof.
  intros x Hx.
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.ltb_spec i 64).
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
    - rewrite Z.ones_spec_high by lia. replace (Z.testbit x i) with false; [reflexivity|]. symmetry.
      apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|].
      apply Z.lt_le_trans with (2^64); [lia|]. apply Z.pow_le_mono_r; lia. }
  replace 18446744073709551615 with (Z.ones 64) by reflexivity. rewrite E, Z.land_ones by lia.
  rewrite Z.lnot_eq_pred_opp. symmetry. apply Z.mod_unique with (q := -1); lia.
Qed.

Ltac take_false tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => replace cnd with false; [cbv iota | symmetry; tac] end.
Ltac take_true tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => replace cnd with true; [cbv iota | symmetry; tac] end.

Definition wsampU (hi mid lo : byte) : word :=
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64
    (Z.shiftl (bv_unsigned (zxb mid)) 8))) (bv_unsigned (zxb lo))))) (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned
    (Z_to_bv 64 (Z.land (bv_unsigned (sxb hi)) 255))) 16))))))
    (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sxb hi)) 18446744073692774400)))).

Lemma wsampU_eq : forall hi mid lo, wsampU hi mid lo = Z_to_bv 64 (samp24 hi mid lo).
Proof.
  intros hi mid lo. rewrite <- wsamp_eq. unfold wsampU, wsamp.
  rewrite (Z.lor_comm (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb mid)) 8)))).
  rewrite (Z.lor_comm (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (zxb lo))
    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb mid)) 8))))))).
  reflexivity.
Qed.

Ltac wsampU_rw := let E := fresh "E" in pose proof wsampU_eq as E; unfold wsampU in E; rewrite E; clear E.

Lemma fr_mergeU : forall mk A V x y1 y2 y3 y4 y5 y6 SV,
  rw_cells rsegs mk A (CB 48 V :: CB 2 x :: C1 y1 :: C1 y2 :: C1 y3 :: C1 y4 :: C1 y5 :: C1 y6 :: SV) ->
  exists J, rw_cells rsegs mk A (CB 48 V :: CB 8 J :: SV).
Proof.
  intros mk A V x y1 y2 y3 y4 y5 y6 SV H.
  pose proof (rw_cells_merge rsegs mk A [CB 48 V] [CB 2 x; C1 y1; C1 y2; C1 y3; C1 y4; C1 y5; C1 y6] SV H) as M.
  eexists. exact M.
Qed.

Ltac nzU i W SL E11 E18 := repeat first [
    rewrite (unsigned_lit i) by lia | rewrite (unsigned_lit (i * W)) by lia | rewrite Z.add_0_r
  | rewrite (sw32 i) by lia | rewrite (sw32 (i * W)) by lia | rewrite E18 | rewrite E11
  | rewrite (sw32 (i * W + SL)) by lia | rewrite (unsigned_lit (i * W + SL)) by lia
  | rewrite (unsigned_lit (SL + W * i)) by lia | rewrite (Z.shiftl_mul_pow2 _ 1) by lia | rewrite (Z.pow_1_r 2) ].

Ltac bvc := unfold bv_ltu, bv_eqb; fold_lit_ux; repeat (match goal with
    | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
    | |- context [Z.lxor ?x 18446744073709551615] => rewrite (lxor_ones x) by lia
    end);
  first [ rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia
        | rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia ]; reflexivity.

Ltac inner_round k0 :=
  step; take_false bvc;
  lazymatch goal with
  | BB : bytes_at rsegs ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let RA := fresh "RA" in let RB := fresh "RB" in
      pose proof (rdz mm _ _ k0 BB ltac:(lia)) as RA; pose proof (rdz mm _ _ (k0 + 1) BB ltac:(lia)) as RB;
      step; step; clear RA RB
  end;
  step; step; step; sbstep; sbstep; step; step; br_eq.

Section LU.
Variables (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra C X11 X18 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte)
  (lo len slot W AT GOT : Z) (f : Z -> Z) (Q : machine_state -> Prop).

Local Notation SP1 := (bv_unsigned sp + -160).
Local Notation c := (bv_unsigned C).
Local Notation V := (le4s f).
Local Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition LINVU (mk : word -> option byte) : Prop :=
  (exists J, rw_cells rsegs mk SP1 (CB 48 V :: CB 8 J :: SAVED)) /\ stk rsegs mk lo SP1 /\ bytes_at rsegs mk c bs /\
  munch [(bv_unsigned sp - 272, bv_unsigned sp)] m mk /\ wmono rsegs m mk /\ mem_inv rsegs mk.

Local Notation LST pc x1 x9 x10 x21 x22 x23 x24 x25 x26 x27 mk :=
  (MS (mkR x1 (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 AT) (Z_to_bv 64 (bv_unsigned sp + -110 + AT)) (Z_to_bv 64 (AT + 1))
           C x9 x10 X11 (Z_to_bv 64 (Z.lxor c 18446744073709551615)) (Z_to_bv 64 (bv_unsigned sp + -110))
           (Z_to_bv 64 (c + 51)) (Z_to_bv 64 12)
           (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -110) 18446744073709551615))
           (Z_to_bv 64 1515870810) X18 (Z_to_bv 64 GOT) (Z_to_bv 64 SP1) x21 x22 x23 x24 x25 x26 x27
           (Z_to_bv 64 (AT + 2)) (Z_to_bv 64 (bv_unsigned sp + -110 + (AT + 1)))
           (Z_to_bv 64 (bv_unsigned sp + -110 + (AT + 2))) (Z_to_bv 64 (-16777216)))
      F (Z_to_bv 64 pc) fc None mk (seg_rom rsegs)).

Hypothesis HSP : 272 <= bv_unsigned sp.
Hypothesis HAT : AT = 3 * (slot mod 2).
Hypothesis HGOT : GOT = 0 \/ GOT = 1.
Hypothesis HF0 : GOT = 0 -> forall i, 0 <= i < 12 -> f i = 0x5a5a5a5a.
Hypothesis HW : GOT = 1 -> 2 <= W <= 40 /\ W mod 2 = 0 /\ 0 <= slot < W /\ 52 + 36 * W <= len.
Hypothesis HL : Z.of_nat (length bs) = len.
Hypothesis HC : 0 <= c /\ c + len <= 2^64.
Hypothesis DJ : c + len <= bv_unsigned sp - 272 \/ bv_unsigned sp <= c.
Hypothesis H11 : GOT = 1 -> bv_unsigned X11 = slot - slot mod 2.
Hypothesis H18 : GOT = 1 -> bv_unsigned X18 = W.
Hypothesis HF1 : GOT = 1 -> forall i, 0 <= i < 12 -> f i = rp_sample bs W slot i.

Lemma cr_loop : forall n i (x1 x9 x21 x22 x23 x24 x25 x26 x27 : word) mk,
  Z.of_nat n = 12 - i -> 0 <= i < 12 -> (GOT = 1 -> x9 = Z_to_bv 64 (slot - slot mod 2 + W * i)) -> LINVU mk ->
  (forall (y1 y9 y10 y21 y22 y23 y24 y25 y26 y27 : word) mk', LINVU mk' ->
     evt rsegs Q (LST 0x134e4 y1 y9 y10 y21 y22 y23 y24 y25 y26 y27 mk')) ->
  evt rsegs Q (LST 0x13410 x1 x9 (Z_to_bv 64 i) x21 x22 x23 x24 x25 x26 x27 mk).
Proof.
  induction n as [|n IH]; intros i x1 x9 x21 x22 x23 x24 x25 x26 x27 mk Hn Hi H9 ((J & FR) & ST & BB & MU & WM & MI) K;
    [lia|].
  pose proof (u64_range sp) as Rsp. pose proof (u64_range C) as RC.
  assert (ATR : AT = 0 \/ AT = 3) by (rewrite HAT; Z.div_mod_to_equations; lia).
  destruct (proj1 (rw_cells_app mk SP1 [CB 48 V] (CB 8 J :: SAVED)) FR) as [[[_ BV] _] _].
  cbn [cells_bytes cbytes] in BV. rewrite app_nil_r in BV.
  pose proof (le4s_read mk SP1 f i BV Hi) as HR. clear BV.
  step. step. rewrite (unsigned_lit i) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  step. clear HR. step. rewrite bveqb_lit by lia.
  destruct HGOT as [G|G]; [rewrite (proj2 (Z.eqb_eq GOT 0) G) | rewrite (proj2 (Z.eqb_neq GOT 0) ltac:(lia))]; cbv iota.
  - step. rewrite (HF0 G i Hi), sx32_lit by lia. rewrite bveqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]; cbv iota.
    do 3 step.
    destruct n as [|n].
    + take_false ltac:(rewrite bveqb_lit by lia; rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity).
      apply K. split; [exists J; exact FR|]. tauto.
    + take_true ltac:(rewrite bveqb_lit by lia; rewrite (proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
      apply (IH (i + 1)); [lia | lia | intros G'; lia | | exact K].
      split; [exists J; exact FR|]. tauto.
  - specialize (H9 G). subst x9. destruct (HW G) as (W1 & W2 & W3 & W4).
    pose proof (H11 G) as E11. pose proof (H18 G) as E18.
    assert (SL : 0 <= slot - slot mod 2 <= W - 2) by (Z.div_mod_to_equations; lia).
    assert (IW : 0 <= W * i <= 11 * W).
    { split; [apply Z.mul_nonneg_nonneg; lia|].
      rewrite (Z.mul_comm 11 W). apply Z.mul_le_mono_nonneg_l; lia. }
    do 4 step. nzU i W (slot - slot mod 2) E11 E18.
    take_false ltac:(rewrite bveqb_lit by lia; rewrite Z.eqb_refl; reflexivity).
    do 4 step. nzU i W (slot - slot mod 2) E11 E18.
    take_false ltac:(rewrite bveqb_lit by lia; rewrite Z.eqb_refl; reflexivity).
    do 5 step. nzU i W (slot - slot mod 2) E11 E18.
    take_false ltac:(unfold bv_ltu; rewrite lxor_ones by lia; rewrite !unsigned_lit by lia; apply Z.ltb_ge; lia).
    do 7 step. nzU i W (slot - slot mod 2) E11 E18.
    inner_round (50 + 3 * (slot - slot mod 2) + 3 * W * i + 0).
    inner_round (50 + 3 * (slot - slot mod 2) + 3 * W * i + 2).
    inner_round (50 + 3 * (slot - slot mod 2) + 3 * W * i + 4).
    do 3 (step; take_false bvc).
    assert (P : slot mod 2 = 0 \/ slot mod 2 = 1) by lia.
    destruct P as [P|P].
    + pose proof (cells_rd1 _ _ _ 51 _ FR ltac:(reflexivity)) as B1.
      pose proof (cells_rd1 _ _ _ 50 _ FR ltac:(reflexivity)) as B0.
      pose proof (cells_rd1 _ _ _ 52 _ FR ltac:(reflexivity)) as B2.
      do 3 step. clear B0 B1 B2.
      do 7 step.
      rewrite (HF1 G i Hi).
      rewrite (rps bs W slot i (Z.to_nat (50 + 3 * (slot - slot mod 2) + 3 * W * i + 3))
                 (Z.to_nat (50 + 3 * (slot - slot mod 2) + 3 * W * i + 0))
                 (Z.to_nat (50 + 3 * (slot - slot mod 2) + 3 * W * i + 1)))
        by (unfold braid_pos; cbv zeta; rewrite P; cbn [Z.eqb Pos.eqb]; f_equal; lia).
      wsampU_rw. rewrite sx32_lit by (match goal with |- context [samp24 ?a ?b ?c] => pose proof (samp24_range a b c) end; lia).
      step. unfold bv_eqb at 1. rewrite Z.eqb_refl. cbn [negb]; cbv iota.
      do 4 step. nzU i W (slot - slot mod 2) E11 E18.
      apply fr_mergeU in FR. destruct FR as [J' FR].
      destruct n as [|n].
      * take_false ltac:(rewrite bveqb_lit by lia; rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity).
        apply K. split; [exists J'; exact FR|]. tauto.
      * take_true ltac:(rewrite bveqb_lit by lia; rewrite (proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
        apply (IH (i + 1)); [lia | lia | | | exact K].
        -- intros _. f_equal. rewrite sw32 by lia. lia.
        -- split; [exists J'; exact FR|]. tauto.
    + pose proof (cells_rd1 _ _ _ 54 _ FR ltac:(reflexivity)) as B1.
      pose proof (cells_rd1 _ _ _ 53 _ FR ltac:(reflexivity)) as B0.
      pose proof (cells_rd1 _ _ _ 55 _ FR ltac:(reflexivity)) as B2.
      do 3 step. clear B0 B1 B2.
      do 7 step.
      rewrite (HF1 G i Hi).
      rewrite (rps bs W slot i (Z.to_nat (50 + 3 * (slot - slot mod 2) + 3 * W * i + 4))
                 (Z.to_nat (50 + 3 * (slot - slot mod 2) + 3 * W * i + 5))
                 (Z.to_nat (50 + 3 * (slot - slot mod 2) + 3 * W * i + 2)))
        by (unfold braid_pos; cbv zeta; rewrite P; cbn [Z.eqb Pos.eqb]; f_equal; lia).
      wsampU_rw. rewrite sx32_lit by (match goal with |- context [samp24 ?a ?b ?c] => pose proof (samp24_range a b c) end; lia).
      step. unfold bv_eqb at 1. rewrite Z.eqb_refl. cbn [negb]; cbv iota.
      do 4 step. nzU i W (slot - slot mod 2) E11 E18.
      apply fr_mergeU in FR. destruct FR as [J' FR].
      destruct n as [|n].
      * take_false ltac:(rewrite bveqb_lit by lia; rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity).
        apply K. split; [exists J'; exact FR|]. tauto.
      * take_true ltac:(rewrite bveqb_lit by lia; rewrite (proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
        apply (IH (i + 1)); [lia | lia | | | exact K].
        -- intros _. f_equal. rewrite sw32 by lia. lia.
        -- split; [exists J'; exact FR|]. tauto.
Qed.
End LU.

Definition cr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - CHECK_READ_STACK, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Section TL.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (bs : list byte) (lo : Z).
Hypothesis H_rp_slot_read : rp_slot_read_contract.
Hypothesis HLO : lo + 272 <= bv_unsigned sp.
Hypothesis Hlo : 0 <= lo.
Hypothesis HSA : bv_unsigned sp mod 16 = 0.
Hypothesis HN : bv_unsigned a1 <= 1600.
Hypothesis H0 : bv_unsigned a0 <> 0.
Hypothesis HL : Z.of_nat (length bs) = bv_unsigned a1.
Hypothesis DJ : bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - 272 \/ bv_unsigned sp <= bv_unsigned a0.

Local Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation Q := (cr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo).
Local Notation V0 := (le4s (fun _ => 1515870810)).

Lemma cr_exit : forall (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
    r28 r29 r30 r31 : word) mk V J,
  rw_cells rsegs mk (bv_unsigned sp + -160) (CB 48 V :: CB 8 J :: SAVED) ->
  stk rsegs mk lo (bv_unsigned sp + -160) ->
  munch [(bv_unsigned sp - 272, bv_unsigned sp)] m mk -> wmono rsegs m mk -> mem_inv rsegs mk ->
  evt rsegs Q (MS (mkR r1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
                       r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
                  F (Z_to_bv 64 0x134e4) fc None mk (seg_rom rsegs)).
Proof.
  intros r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
    mk V J FR ST MU WM MI.
  pose proof (u64_range sp) as Rsp.
  do 15 step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold cr_post, CHECK_READ_STACK.
  exists r5, r6, r7, r10, r11, r12, r13, r14, r15, r16, r17, r28, r29, r30, r31, mk.
  split; [reflexivity|]. tauto.
Qed.

Lemma cr_tail : forall (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word) m1 J,
  rw_cells rsegs m1 (bv_unsigned sp + -160) (CB 48 V0 :: CB 8 J :: SAVED) ->
  stk rsegs m1 lo (bv_unsigned sp + -160) -> bytes_at rsegs m1 (bv_unsigned a0) bs ->
  munch [(bv_unsigned sp - 272, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  x19 = Z_to_bv 64 (rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2)) ->
  (rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2) = 1 ->
     x18 = Z_to_bv 64 (rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2))) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp x5 x6 x7 a0 a2 x10 a1 x12 x13
                       x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x133ac) fc None m1 (seg_rom rsegs)).
Proof.
  intros x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m1 J FR ST BB MU WM MI E19 E18.
  subst x19.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  do 5 step.
  eapply evt_cut.
  { eapply H_rp_slot_read with (lo := lo) (bs := bs); rewrite ?(unsigned_lit (bv_unsigned sp + -160)) by lia.
    - exact MI.
    - exact ST.
    - lia.
    - intros _. split; [exact H0|]. split; [lia|]. split; [exact BB | lia].
    - intros _. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
      split; [eapply rw_cells_wr; [exact FR | cbn; lia]|]. split; lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & WM2 & MI2 & ST2 & HM).
  rewrite (unsigned_lit (bv_unsigned sp + -160)) in ST2, HM by lia.
  replace (ret_pc (Z_to_bv 64 78784)) with (Z_to_bv 64 78784) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. unfold bv_eqb at 1. rewrite Z.eqb_refl. cbn [negb]; cbv iota.
  do 19 step.
  rewrite at_bits. rewrite (unsigned_lit (bv_unsigned sp + -110)) by lia.
  destruct (Z.leb_spec 0 (rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2))) as [WP|WN].
  - assert (G : rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2) = 1)
      by (unfold rp_slot_read_model; rewrite (proj2 (Z.ltb_ge _ 0) WP); reflexivity).
    rewrite (E18 G). try rewrite (proj2 (Z.leb_le _ _) WP) in HM. cbv iota in HM. destruct HM as [MU2 BV2].
    destruct (width_facts (bv_unsigned a1) bs (bv_signed a2) ltac:(lia) WP) as (W1 & W2 & W3 & W4 & W5).
    apply (proj1 (rw_cells_app m1 _ [_] _)) in FR. destruct FR as [FRv FRr].
    cbn [cells_size csize Nat.add] in FRr.
    pose proof (rw_cells_transport rsegs _ _ _ _ _ FRr MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | split; [lia | exact I]])) as FRr2.
    pose proof (rw_cells_CB m2 _ _ 48 (rp_slot_bytes_length _ _ _) BV2
                  (wr_at_transport rsegs _ _ _ _ (rw_cells_wr _ _ _ 48 FRv ltac:(cbn; lia)) WM2)) as FRv2.
    pose proof (proj2 (rw_cells_app m2 _ [_] _) (conj FRv2 FRr2)) as FR2. cbn [app] in FR2.
    pose proof (bytes_at_transport rsegs _ _ _ _ _ BB MU2
                  ltac:(cbn [disjoint_from]; rewrite HL; split; [lia | split; [lia | exact I]])) as BB2.
    assert (MU3 : munch [(bv_unsigned sp - 272, bv_unsigned sp)] m m2)
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MU2];
          intros x Hx; cbn [outside] in *; destruct Hx as [Hx _]; split; [lia | split; [lia | exact I]]).
    pose proof (wmono_trans _ _ _ _ WM WM2) as WM3.
    clear FRv FRr FRr2 FRv2 BV2 MU2 BB MU WM ST MI.
    rewrite G.
    pose proof (signed_nonneg a2 ltac:(lia)) as SU.
    eapply cr_loop with (n := 12%nat) (i := 0) (lo := lo) (m := m) (bs := bs)
      (len := bv_unsigned a1) (slot := bv_signed a2) (W := rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2))
      (AT := 3 * (bv_signed a2 mod 2)) (GOT := 1)
      (f := fun i => rp_sample bs (rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)) (bv_signed a2) i)
      (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8)
      (s9 := s9) (s10 := s10) (s11 := s11) (ra := ra).
    + lia.
    + reflexivity.
    + right; reflexivity.
    + intros E; discriminate E.
    + intros _. split; [lia|]. split; [exact W2|]. split; [lia | lia].
    + exact HL.
    + pose proof (bytes_at_bound _ _ _ _ BB2). lia.
    + exact DJ.
    + intros _. rewrite SU, land_m2 by lia. rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
      Z.div_mod_to_equations. lia.
    + intros _. apply unsigned_lit. lia.
    + intros _ i Hi. reflexivity.
    + reflexivity.
    + lia.
    + intros _. rewrite SU, land_m2 by lia. f_equal. Z.div_mod_to_equations. lia.
    + split; [exists J; exact FR2|]. split; [exact ST2|]. split; [exact BB2|]. split; [exact MU3|].
      split; [exact WM3 | exact MI2].
    + intros y1 y9 y10 y21 y22 y23 y24 y25 y26 y27 mk' ((J' & FR') & ST' & _ & MU' & WM' & MI').
      eapply cr_exit; eassumption.
  - assert (G : rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2) = 0)
      by (unfold rp_slot_read_model; rewrite (proj2 (Z.ltb_lt _ 0) WN); reflexivity).
    try rewrite (proj2 (Z.leb_gt _ _) WN) in HM. cbv iota in HM. rename HM into MU2.
    pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I])) as FR2.
    pose proof (bytes_at_transport rsegs _ _ _ _ _ BB MU2
                  ltac:(cbn [disjoint_from]; rewrite HL; split; [lia | exact I])) as BB2.
    assert (MU3 : munch [(bv_unsigned sp - 272, bv_unsigned sp)] m m2)
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MU2];
          intros x Hx; cbn [outside] in *; destruct Hx as [Hx _]; split; [lia | exact I]).
    pose proof (wmono_trans _ _ _ _ WM WM2) as WM3.
    clear MU2 BB MU WM ST MI FR.
    rewrite G.
    eapply cr_loop with (n := 12%nat) (i := 0) (lo := lo) (m := m) (bs := bs)
      (len := bv_unsigned a1) (slot := bv_signed a2) (W := 0)
      (AT := 3 * (bv_signed a2 mod 2)) (GOT := 0) (f := fun _ => 1515870810)
      (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8)
      (s9 := s9) (s10 := s10) (s11 := s11) (ra := ra).
    + lia.
    + reflexivity.
    + left; reflexivity.
    + intros _ i Hi. reflexivity.
    + intros E; discriminate E.
    + exact HL.
    + pose proof (bytes_at_bound _ _ _ _ BB2). lia.
    + exact DJ.
    + intros E; discriminate E.
    + intros E; discriminate E.
    + intros E; discriminate E.
    + reflexivity.
    + lia.
    + intros E; discriminate E.
    + split; [exists J; exact FR2|]. split; [exact ST2|]. split; [exact BB2|]. split; [exact MU3|].
      split; [exact WM3 | exact MI2].
    + intros y1 y9 y10 y21 y22 y23 y24 y25 y26 y27 mk' ((J' & FR') & ST' & _ & MU' & WM' & MI').
      eapply cr_exit; eassumption.
Qed.

Local Notation ST1 pc x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m1 :=
  (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp x5 x6 x7 a0 a2 x10 a1 x12 x13
           x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

Lemma cr_zero : forall (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word) m1 J,
  rw_cells rsegs m1 (bv_unsigned sp + -160) (CB 48 V0 :: CB 8 J :: SAVED) ->
  stk rsegs m1 lo (bv_unsigned sp + -160) -> bytes_at rsegs m1 (bv_unsigned a0) bs ->
  munch [(bv_unsigned sp - 272, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2) = 0 ->
  evt rsegs Q (ST1 0x133a8 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m1).
Proof.
  intros x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m1 J FR ST BB MU WM MI G.
  step. eapply cr_tail; try eassumption.
  - rewrite G. reflexivity.
  - intros E. rewrite G in E. discriminate E.
Qed.

Lemma cr_b16 : forall (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) m1 J W,
  rw_cells rsegs m1 (bv_unsigned sp + -160) (CB 48 V0 :: CB 8 J :: SAVED) ->
  stk rsegs m1 lo (bv_unsigned sp + -160) -> bytes_at rsegs m1 (bv_unsigned a0) bs ->
  munch [(bv_unsigned sp - 272, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  50 <= bv_unsigned a1 -> W = w_width_model (bv_unsigned a1) -> (W = -1 \/ 2 <= W <= 40) ->
  evt rsegs Q (ST1 0x13398 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 W) x19 x28 x29 x30 x31 m1).
Proof.
  intros x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m1 J W FR ST BB MU WM MI H50 EW RW.
  pose proof (u64_range a0) as Ra0. pose proof (bytes_at_bound _ _ _ _ BB) as BBB.
  step. step. take_false bvc.
  pose proof (rdz m1 _ bs 16 BB ltac:(lia)) as R16.
  step. clear R16. step.
  unfold zxb. rewrite bveqb_lit by (pose proof (byte_range (nth (Z.to_nat 16) bs (Z_to_bv 8 0))); lia).
  change (Z.to_nat 16) with 16%nat.
  assert (E16 : slot_byte bs 16 = bv_unsigned (nth 16 bs (Z_to_bv 8 0))) by reflexivity.
  assert (SW : bv_swrap 64 (bv_unsigned a1) = bv_unsigned a1)
    by (apply bv_swrap_small; change (bv_half_modulus 64) with (2^63); lia).
  destruct (ww_facts (bv_unsigned a1) ltac:(lia)) as [WF _]. rewrite <- EW in WF.
  destruct (Z.eqb_spec (bv_unsigned (nth 16 bs (Z_to_bv 8 0))) 0) as [B16|B16]; cbv iota.
  - step. step. take_false bvc. step. step. unfold bv_lts. rewrite (signed_lit 0) by lia.
    destruct (Z.ltb_spec (bv_signed a2) 0) as [SN|SN]; cbv iota.
    + eapply cr_tail; try eassumption.
      * symmetry. f_equal. apply srm_zero. right; right; right; left. exact SN.
      * intros E. rewrite srm_zero in E by (right; right; right; left; exact SN). discriminate E.
    + pose proof (rdz m1 _ bs 17 BB ltac:(lia)) as R17.
      step. clear R17. step.
      unfold zxb. rewrite bveqb_lit by (pose proof (byte_range (nth (Z.to_nat 17) bs (Z_to_bv 8 0))); lia).
      change (Z.to_nat 17) with 17%nat.
      destruct (Z.eqb_spec (bv_unsigned (nth 17 bs (Z_to_bv 8 0))) 0) as [B17|B17]; cbn [negb]; cbv iota.
      * step. unfold bv_lts. rewrite (signed_lit 0), (signed_lit W) by lia.
        assert (FC : rp_frame_channels_model (bv_swrap 64 (bv_unsigned a1)) = W) by (rewrite SW; congruence).
        destruct RW as [RW|RW].
        -- rewrite (proj2 (Z.ltb_ge 0 W)) by lia. cbn [negb]; cbv iota.
           eapply cr_tail; try eassumption.
           ++ symmetry. f_equal. apply srm_zero. right; right; right; right; left. lia.
           ++ intros E. rewrite srm_zero in E by (right; right; right; right; left; lia). discriminate E.
        -- rewrite (proj2 (Z.ltb_lt 0 W)) by lia. cbn [negb]; cbv iota.
           step. step.
           pose proof (signed_nonneg a2 SN) as SU.
           destruct (Z.ltb_spec (bv_signed a2) W) as [LT|GE].
           ++ destruct (srm_one (bv_unsigned a1) bs (bv_signed a2) H50 ltac:(lia) ltac:(exact B17) ltac:(lia))
                as [M1 M2].
              eapply cr_tail; try eassumption.
              ** rewrite M1, v_sltu_b2z, SU, unsigned_lit by lia. rewrite (proj2 (Z.ltb_lt _ _) LT). reflexivity.
              ** intros _. rewrite M2, FC. reflexivity.
           ++ eapply cr_tail; try eassumption.
              ** rewrite srm_zero by (right; right; right; right; right; lia).
                 rewrite v_sltu_b2z, SU, unsigned_lit by lia. rewrite (proj2 (Z.ltb_ge _ _) GE). reflexivity.
              ** intros E. rewrite srm_zero in E by (right; right; right; right; right; lia). discriminate E.
      * eapply cr_tail; try eassumption.
        -- symmetry. f_equal. apply srm_zero. right; right; left. exact B17.
        -- intros E. rewrite srm_zero in E by (right; right; left; exact B17). discriminate E.
  - eapply cr_zero; try eassumption. apply srm_zero. right; left. lia.
Qed.
End TL.

Section CR.
Hypothesis H_rp_slot_read : rp_slot_read_contract.

Theorem check_read_holds : check_read_contract.
Proof.
  unfold check_read_contract, CHECK_READ, CHECK_READ_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    MI ST LO SA HN H0 HL BB DJ.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 160%nat ST.
  do 20 step.
  do 11 (step; step; step; br_eq).
  step; step; step. br_eq.
  pose proof (rw_cells_merge rsegs _ _ [] (repeat (C4 (Z_to_bv 64 1515870810)) 12) _ FR) as M. clear FR.
  cbn [app] in M. change (cells_size (repeat (C4 (Z_to_bv 64 1515870810)) 12)) with 48%nat in M.
  change (cells_bytes (repeat (C4 (Z_to_bv 64 1515870810)) 12)) with (le4s (fun _ => 1515870810)) in M.
  do 6 step.
  eapply ww_loopU with (j := 19%nat) (k := 0) (len := bv_unsigned a1).
  - lia.
  - reflexivity.
  - lia.
  - intros x10 x14 n E R.
    change (ww_go 20 (2 + 2 * 0) (bv_unsigned a1)) with (w_width_model (bv_unsigned a1)) in E.
    destruct (ww_facts (bv_unsigned a1) ltac:(lia)) as [_ WF2]. rewrite E in WF2.
    eapply cr_b16 with (W := n) (bs := bs) (lo := lo) (m := m); try eassumption; lia.
  - intros x10 x14 x18 E.
    change (ww_go 20 (2 + 2 * 0) (bv_unsigned a1)) with (w_width_model (bv_unsigned a1)) in E.
    do 3 step. unfold bv_ltu. rewrite (unsigned_lit 49) by lia.
    destruct (Z.ltb_spec 49 (bv_unsigned a1)); cbn [negb]; cbv iota.
    + eapply cr_b16 with (W := -1) (bs := bs) (lo := lo) (m := m); try eassumption; lia.
    + eapply cr_zero with (bs := bs) (lo := lo) (m := m); try eassumption; first [lia | apply srm_zero; left; lia].
Qed.
End CR.

