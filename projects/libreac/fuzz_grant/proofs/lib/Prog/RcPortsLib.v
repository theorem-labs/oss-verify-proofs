From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcLib RcPorts.
Import ListNotations.
Open Scope Z_scope.

Lemma rc_word : forall (x : word) z, bv_unsigned x = z -> x = Z_to_bv 64 z.
Proof. intros x z <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma rc_word_range : forall (x : word) z, bv_unsigned x = z -> 0 <= z < 2^64.
Proof. intros x z <-. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. exact R. Qed.

Lemma rc_firstn_skipn : forall (bs : list byte) n k, (k + n <= length bs)%nat ->
  firstn n (skipn k bs) = map (fun i => nth i bs (Z_to_bv 8 0)) (seq k n).
Proof.
  intros bs n. induction n as [|n IH]; intros k Hk; [reflexivity|].
  rewrite <- (firstn_skipn_step bs k n (nth k bs (Z_to_bv 8 0))).
  - cbn [seq map]. f_equal. apply IH. lia.
  - apply nth_error_nth'. lia.
Qed.

Lemma rc_rd4 : forall segs m A (bs : list byte) k, bytes_at segs m A bs -> (k + 4 <= length bs)%nat ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) 4 =
    Some [nth k bs (Z_to_bv 8 0); nth (k + 1) bs (Z_to_bv 8 0); nth (k + 2) bs (Z_to_bv 8 0);
          nth (k + 3) bs (Z_to_bv 8 0)].
Proof.
  intros segs m A bs k HB Hk. rewrite (bytes_at_read segs m A bs (Z.of_nat k) 4 HB) by lia.
  rewrite Nat2Z.id, rc_firstn_skipn by lia. cbn [seq map].
  replace (k + 1)%nat with (S k) by lia. replace (k + 2)%nat with (S (S k)) by lia.
  replace (k + 3)%nat with (S (S (S k))) by lia. reflexivity.
Qed.

Lemma rc_lw4 : forall b0 b1 b2 b3 : byte,
  sext 64 (bv_extract 0 32 (le_bytes_to_word [b0; b1; b2; b3])) =
    Z_to_bv 64 (rc_s32of (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2) (bv_unsigned b3)).
Proof.
  intros b0 b1 b2 b3. rewrite sext_small, signed_of_extract by lia. f_equal.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned, bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1.
  pose proof (byte_range b2) as R2. pose proof (byte_range b3) as R3.
  set (x0 := bv_unsigned b0) in *. set (x1 := bv_unsigned b1) in *.
  set (x2 := bv_unsigned b2) in *. set (x3 := bv_unsigned b3) in *.
  unfold rc_s32of, bv_swrap, bv_wrap. cbv zeta.
  change (bv_modulus 64) with 18446744073709551616.
  change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296.
  rewrite (Z.mod_small (x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * 0)))) 18446744073709551616) by lia.
  destruct (Z.ltb_spec (x0 + 256 * x1 + 65536 * x2 + 16777216 * x3) 2147483648) as [L|L].
  - rewrite Z.mod_small by lia. lia.
  - Z.div_mod_to_equations. lia.
Qed.

Lemma rc_rd4_opaque : forall segs m A (bs : list byte) k, bytes_at segs m A bs -> (k + 4 <= length bs)%nat ->
  exists L, L = [nth k bs (Z_to_bv 8 0); nth (k + 1) bs (Z_to_bv 8 0); nth (k + 2) bs (Z_to_bv 8 0);
                 nth (k + 3) bs (Z_to_bv 8 0)] /\
            ov_read_bytes segs m (wa (A + Z.of_nat k)) 4 = Some L.
Proof. intros segs m A bs k HB Hk. eexists. split; [reflexivity|]. apply rc_rd4; assumption. Qed.

Lemma rc_lw_s32 : forall (bs : list byte) k L,
  L = [nth k bs (Z_to_bv 8 0); nth (k + 1) bs (Z_to_bv 8 0); nth (k + 2) bs (Z_to_bv 8 0);
       nth (k + 3) bs (Z_to_bv 8 0)] ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word L)) =
    Z_to_bv 64 (rc_s32of (rc_u8 bs k) (rc_u8 bs (k + 1)) (rc_u8 bs (k + 2)) (rc_u8 bs (k + 3))).
Proof. intros bs k L ->. apply rc_lw4. Qed.

Lemma rc_lw_in : forall (bs : list byte) L,
  L = [nth 0 bs (Z_to_bv 8 0); nth 1 bs (Z_to_bv 8 0); nth 2 bs (Z_to_bv 8 0); nth 3 bs (Z_to_bv 8 0)] ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word L)) = Z_to_bv 64 (bm_in_ch bs).
Proof. intros bs L EL. exact (rc_lw_s32 bs 0 L EL). Qed.

Lemma rc_lw_out : forall (bs : list byte) L,
  L = [nth 4 bs (Z_to_bv 8 0); nth 5 bs (Z_to_bv 8 0); nth 6 bs (Z_to_bv 8 0); nth 7 bs (Z_to_bv 8 0)] ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word L)) = Z_to_bv 64 (bm_out_ch bs).
Proof. intros bs L EL. exact (rc_lw_s32 bs 4 L EL). Qed.

Lemma rc_s32of_range : forall u0 u1 u2 u3, 0 <= u0 < 256 -> 0 <= u1 < 256 -> 0 <= u2 < 256 -> 0 <= u3 < 256 ->
  -2147483648 <= rc_s32of u0 u1 u2 u3 < 2147483648.
Proof.
  intros u0 u1 u2 u3 H0 H1 H2 H3. unfold rc_s32of. cbv zeta.
  destruct (Z.ltb_spec (u0 + 256 * u1 + 65536 * u2 + 16777216 * u3) 2147483648); lia.
Qed.

Lemma bm_in_ch_range : forall bs, -2147483648 <= bm_in_ch bs < 2147483648.
Proof. intros bs. unfold bm_in_ch, rc_u8. apply rc_s32of_range; apply byte_range. Qed.

Lemma bm_out_ch_range : forall bs, -2147483648 <= bm_out_ch bs < 2147483648.
Proof. intros bs. unfold bm_out_ch, rc_u8. apply rc_s32of_range; apply byte_range. Qed.

Lemma rc_eqb : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rc_ltu : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rc_lts0 : forall x, -2^63 <= x < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0) = (x <? 0).
Proof.
  intros x Hx. rewrite bv_lts_zero_r, unsigned_lit_wrap.
  destruct (Z.ltb_spec x 0).
  - apply Z.leb_le. Z.div_mod_to_equations. lia.
  - apply Z.leb_gt. rewrite Z.mod_small by lia. lia.
Qed.

Lemma rc_swrap32 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia. Qed.

Lemma rc_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma rc_odd_eqb : forall x, 0 <= x < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 1)) (Z_to_bv 64 0) = (x mod 2 =? 0).
Proof.
  intros x Hx. rewrite unsigned_lit by lia. rewrite rc_land1.
  pose proof (Z.mod_pos_bound x 2 ltac:(lia)). apply rc_eqb; lia.
Qed.

Lemma rc_wok_ltu : forall w, 0 <= w < 2^31 ->
  bv_ltu (Z_to_bv 64 (w + -41)) (Z_to_bv 64 (-39)) = negb ((2 <=? w) && (w <=? 40)).
Proof.
  intros w Hw. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  change (2^64) with 18446744073709551616.
  replace ((-39) mod 18446744073709551616) with 18446744073709551577 by reflexivity.
  destruct (Z.leb_spec 2 w); destruct (Z.leb_spec w 40); cbn [andb negb];
    [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.ltb_lt | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma rc_addiw : forall x d, 0 <= x < 2^64 -> -2^31 <= x + d < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + d)) = Z_to_bv 64 (x + d).
Proof. intros x d Hx Hd. rewrite unsigned_lit by lia. rewrite rc_swrap32 by lia. reflexivity. Qed.

Lemma rc_align8 : forall x, 0 <= x < 2^64 -> x mod 8 = 0 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 7)) (Z_to_bv 64 0) = true.
Proof.
  intros x Hx H8. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2^3) with 8. rewrite H8. reflexivity.
Qed.

Lemma rc_slliw2 : forall n, 0 <= n <= 2^28 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 2)) = Z_to_bv 64 (4 * n).
Proof.
  intros n Hn. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite rc_swrap32 by lia. f_equal. lia.
Qed.

Lemma rc_byte_lit : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma rc_u8_range : forall bs i, 0 <= rc_u8 bs i < 256.
Proof. intros bs i. unfold rc_u8. apply byte_range. Qed.

Lemma rc_zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. pose proof (byte_range b). apply unsigned_lit. lia. Qed.

Lemma rc_u8_eqb : forall bs i z, 0 <= z < 2^64 ->
  bv_eqb (zxb (nth i bs (Z_to_bv 8 0))) (Z_to_bv 64 z) = (rc_u8 bs i =? z).
Proof. intros bs i z Hz. unfold zxb. pose proof (rc_u8_range bs i). unfold rc_u8 in *. apply rc_eqb; lia. Qed.

Lemma rc_u8_ltu : forall bs i z, 0 <= z < 2^64 ->
  bv_ltu (zxb (nth i bs (Z_to_bv 8 0))) (Z_to_bv 64 z) = (rc_u8 bs i <? z).
Proof. intros bs i z Hz. unfold zxb. pose proof (rc_u8_range bs i). unfold rc_u8 in *. apply rc_ltu; lia. Qed.

Lemma rc_decl_ltu : forall u, 0 <= u < 256 ->
  bv_ltu (Z_to_bv 64 4) (Z_to_bv 64 (u + -128)) = negb ((128 <=? u) && (u <=? 132)).
Proof.
  intros u Hu. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (4 mod 18446744073709551616) with 4.
  destruct (Z.leb_spec 128 u); destruct (Z.leb_spec u 132); cbn [andb negb];
    [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.ltb_lt | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma pu_nunk_range : forall bs k, 0 <= pu_nunk bs k <= Z.of_nat k.
Proof.
  intros bs k. induction k as [|k IH]; cbn [pu_nunk]; [lia|].
  destruct (4 <=? rc_u8 bs (8 + k)); lia.
Qed.

Lemma pu_nunk_unk : forall bs k, 4 <= rc_u8 bs (8 + k) -> pu_nunk bs (S k) = pu_nunk bs k + 1.
Proof. intros bs k H. cbn [pu_nunk]. rewrite (proj2 (Z.leb_le 4 _) H). reflexivity. Qed.

Lemma pu_nunk_known : forall bs k, rc_u8 bs (8 + k) < 4 -> pu_nunk bs (S k) = pu_nunk bs k.
Proof. intros bs k H. cbn [pu_nunk]. rewrite (proj2 (Z.leb_gt 4 _) H). lia. Qed.

Lemma pu_first_new : forall bs k, pu_nunk bs k = 0 -> 4 <= rc_u8 bs (8 + k) ->
  pu_first bs (S k) = rc_u8 bs (8 + k).
Proof.
  intros bs k H0 H4. cbn [pu_first]. rewrite H0, (proj2 (Z.leb_le 4 _) H4). reflexivity.
Qed.

Lemma pu_first_keep : forall bs k, ~ (pu_nunk bs k = 0 /\ 4 <= rc_u8 bs (8 + k)) ->
  pu_first bs (S k) = pu_first bs k.
Proof.
  intros bs k H. cbn [pu_first].
  destruct (Z.eqb_spec (pu_nunk bs k) 0); destruct (Z.leb_spec 4 (rc_u8 bs (8 + k))); cbn [andb];
    [exfalso; apply H; split; assumption | reflexivity | reflexivity | reflexivity].
Qed.

Definition rc_wr (segs : list Segment) (c : Z) (m m1 : word -> option byte) : Prop :=
  munch [(c, c + 1)] m m1 /\ wmono segs m m1 /\
  (forall lo hi, stk segs m lo hi -> stk segs m1 lo hi) /\
  (mem_inv segs m -> mem_inv segs m1).

Definition rc_inv (segs : list Segment) (c : Z) (m mc : word -> option byte) (v : Z) : Prop :=
  (c = 0 /\ mc = m) \/
  (c <> 0 /\ rc_wr segs c m mc /\ wr_at segs mc c 1 /\ bytes_at segs mc c [Z_to_bv 8 v]).

Lemma rc_wr_refl : forall segs c m, rc_wr segs c m m.
Proof.
  intros segs c m. split; [apply munch_refl|]. split; [apply wmono_refl|].
  split; [intros lo hi H; exact H | intros H; exact H].
Qed.

Lemma rc_store_ok : forall segs m c, wr_at segs m c 1 -> store_ok segs m (wa c) 1 = true.
Proof.
  intros segs m c HW. pose proof (wr_at_store_ok segs m c 1 0 1 HW ltac:(lia) ltac:(lia)) as S.
  rewrite Z.add_0_r in S. exact S.
Qed.

Lemma rc_wr_write : forall segs c m m1 b, 0 <= c -> c + 1 <= 2^64 -> wr_at segs m1 c 1 -> rc_wr segs c m m1 ->
  rc_wr segs c m (write_to_mem m1 (wa c) [b]).
Proof.
  intros segs c m m1 b H0 H1 HW (MU & WM & ST & MI).
  split; [|split; [|split]].
  - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; left; lia].
  - apply wmono_write. exact WM.
  - intros lo hi Hs. apply stk_write; [apply ST; exact Hs | lia | cbn [length]; lia].
  - intros Hm. apply mem_inv_store; [apply MI; exact Hm | apply rc_store_ok; exact HW].
Qed.

Lemma rc_inv_write : forall segs c m mc b, c <> 0 -> 0 <= c < 2^64 ->
  rc_wr segs c m mc -> wr_at segs mc c 1 ->
  rc_inv segs c m (write_to_mem mc (wa c) [b]) (bv_unsigned b).
Proof.
  intros segs c m mc b Hc Hr W HW. right. split; [exact Hc|].
  split; [apply rc_wr_write; [lia | lia | exact HW | exact W]|]. split.
  - apply wr_at_write. exact HW.
  - rewrite rc_byte_lit. apply bytes_at_write_same; cbn [length]; lia.
Qed.

Lemma rc_inv_store : forall segs c m mc v b, c <> 0 -> 0 <= c < 2^64 -> rc_inv segs c m mc v ->
  rc_inv segs c m (write_to_mem mc (wa c) [b]) (bv_unsigned b).
Proof.
  intros segs c m mc v b Hc Hr [[E _]|(_ & W & HW & _)]; [contradiction|].
  apply rc_inv_write; assumption.
Qed.

Lemma rc_inv_first : forall segs c m b, c <> 0 -> 0 <= c < 2^64 -> wr_at segs m c 1 ->
  rc_inv segs c m (write_to_mem m (wa c) [b]) (bv_unsigned b).
Proof. intros segs c m b Hc Hr HW. apply rc_inv_write; [exact Hc | exact Hr | apply rc_wr_refl | exact HW]. Qed.

Lemma rc_inv_c0 : forall segs m v, rc_inv segs 0 m m v.
Proof. intros segs m v. left. split; reflexivity. Qed.

Lemma rc_inv_same : forall segs c m mc v v', (c = 0 \/ v = v') -> rc_inv segs c m mc v -> rc_inv segs c m mc v'.
Proof.
  intros segs c m mc v v' [E|E] H.
  - destruct H as [H|(Hc & _)]; [left; exact H | contradiction].
  - subst v'. exact H.
Qed.

Lemma rc_inv_store_ok : forall segs c m mc v, c <> 0 -> rc_inv segs c m mc v -> store_ok segs mc (wa c) 1 = true.
Proof.
  intros segs c m mc v Hc [[E _]|(_ & _ & HW & _)]; [contradiction|]. apply rc_store_ok. exact HW.
Qed.

Lemma rc_inv_post : forall segs c m mc v, rc_inv segs c m mc v ->
  munch (if c =? 0 then [] else [(c, c + 1)]) m mc /\ wmono segs m mc /\
  (forall lo hi, stk segs m lo hi -> stk segs mc lo hi) /\ (mem_inv segs m -> mem_inv segs mc) /\
  (c <> 0 -> bytes_at segs mc c [Z_to_bv 8 v]).
Proof.
  intros segs c m mc v [[E Em]|(Hc & (MU & WM & ST & MI) & HW & HB)].
  - subst c mc. rewrite Z.eqb_refl. cbv iota. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [intros lo hi H; exact H|]. split; [intros H; exact H|]. intros H. exfalso. apply H. reflexivity.
  - rewrite (proj2 (Z.eqb_neq c 0) Hc). split; [exact MU|]. split; [exact WM|]. split; [exact ST|].
    split; [exact MI|]. intros _. exact HB.
Qed.

Lemma rc_eqb_neg : forall x y, 0 <= x -> -2^64 < y < 0 -> x < 2^64 + y ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy Hxy. unfold bv_eqb. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma rc_ltu_neg : forall x y, 0 <= x -> -2^64 < y < 0 -> x <= 2^64 + y ->
  bv_ltu (Z_to_bv 64 y) (Z_to_bv 64 x) = false.
Proof.
  intros x y Hx Hy Hxy. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Lemma rc_lts_nn : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed. rewrite !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt x (2^63)) ltac:(lia)), (proj2 (Z.ltb_lt y (2^63)) ltac:(lia)). reflexivity.
Qed.

Lemma rc_sltiu_m8 : forall x, 0 <= x -> x + 20 <= 2^64 -> v_sltiu (Z_to_bv 64 x) (-8) = Z_to_bv 64 1.
Proof.
  intros x Hx Hx20. rewrite v_sltiu_b2z. rewrite unsigned_lit by lia.
  change (bv_wrap 64 (-8)) with 18446744073709551608.
  rewrite (proj2 (Z.ltb_lt x 18446744073709551608)) by lia. reflexivity.
Qed.

Lemma rc_ori4 : forall u, 0 <= u < 256 -> (Z.lor u 4 =? 132) = ((u =? 128) || (u =? 132)).
Proof.
  intros u Hu.
  assert (C : forallb (fun u => Bool.eqb (Z.lor u 4 =? 132) ((u =? 128) || (u =? 132)))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C.
  assert (I : In u (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat u). split; [lia | apply in_seq; lia]. }
  apply Bool.eqb_prop. apply C. exact I.
Qed.

Lemma rc_ori4_eqb : forall u, 0 <= u < 256 ->
  bv_eqb (Z_to_bv 64 (Z.lor u 4)) (Z_to_bv 64 132) = ((u =? 128) || (u =? 132)).
Proof.
  intros u Hu. pose proof (lor_lt_pow2 u 4 8 ltac:(lia) ltac:(lia)) as R.
  rewrite rc_eqb by lia. apply rc_ori4. exact Hu.
Qed.

Lemma rc_mul4_ok : forall n, 0 <= n < 536870912 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (n + 536870912)))) 30)) = Z_to_bv 64 0.
Proof.
  intros n Hn. rewrite unsigned_lit by lia. unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma rc_land_ones64 : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 (bv_unsigned (Z_to_bv 64 x)) = x.
Proof.
  intros x Hx. rewrite unsigned_lit by lia. rewrite Z.land_comm.
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma bm_uw_range : forall mp bs, bm_uw mp bs = 0 \/ (2 <= bm_uw mp bs <= 40 /\ bm_uw mp bs mod 2 = 0).
Proof.
  intros mp bs. unfold bm_uw, bm_wok.
  destruct (mp =? 0); [left; reflexivity|].
  destruct (Z.ltb_spec (bm_in_ch bs) 0); cbn [orb]; [left; reflexivity|].
  destruct (Z.ltb_spec (bm_out_ch bs) 0); cbn [orb]; [left; reflexivity|].
  destruct (Z.eqb_spec (bm_in_ch bs) 0) as [Z0|Z0]; cbn [negb andb].
  - lazymatch goal with |- context [if ?b then 0 else Z.max _ _] => destruct b end; [left; reflexivity|].
    right. rewrite Z0. split; [lia | reflexivity].
  - destruct (Z.leb_spec 2 (bm_in_ch bs)); destruct (Z.leb_spec (bm_in_ch bs) 40);
      destruct (Z.eqb_spec (bm_in_ch bs mod 2) 0); cbn [andb negb]; try (left; reflexivity).
    lazymatch goal with |- context [if ?b then 0 else Z.max _ _] => destruct b end; [left; reflexivity|].
    right. rewrite Z.max_l by lia. split; [lia | assumption].
Qed.
