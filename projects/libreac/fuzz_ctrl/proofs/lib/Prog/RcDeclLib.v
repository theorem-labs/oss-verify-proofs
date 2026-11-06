From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcDecl.
Import ListNotations.
Open Scope Z_scope.

Lemma rc_firstn_cons : forall (bs : list byte) k n, (k < length bs)%nat ->
  firstn (S n) (skipn k bs) = nth k bs (Z_to_bv 8 0) :: firstn n (skipn (S k) bs).
Proof.
  intros bs k n Hk. symmetry. apply firstn_skipn_step. apply nth_error_nth'. exact Hk.
Qed.

Lemma rc_le1_lit : forall z, 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma rc_le_word4 : forall b0 b1 b2 b3 : byte,
  bv_unsigned (le_bytes_to_word [b0; b1; b2; b3]) =
  bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.
Proof.
  intros b0 b1 b2 b3. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned, bytes_le_to_Z_le_val.
  cbn [map le_val].
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  rewrite bv_wrap_small; [lia|]. unfold bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. lia.
Qed.

Lemma rc_u4_range : forall b0 b1 b2 b3 : byte,
  0 <= bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3 < 2^32.
Proof.
  intros. pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  lia.
Qed.

Lemma rc_swrap_s32 : forall u, 0 <= u < 2^32 -> bv_swrap 32 u = s32 u.
Proof.
  intros u Hu. unfold bv_swrap, s32. change (bv_half_modulus 32) with 2147483648.
  unfold bv_wrap. change (bv_modulus 32) with 4294967296. change (2^31) with 2147483648. change (2^32) with 4294967296 in *.
  destruct (Z.ltb_spec u 2147483648).
  - rewrite Z.mod_small by lia. lia.
  - replace (u + 2147483648) with ((u - 2147483648) + 1 * 4294967296) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma rc_lw : forall b0 b1 b2 b3 : byte,
  sext 64 (bv_extract 0 32 (le_bytes_to_word [b0; b1; b2; b3])) =
  Z_to_bv 64 (s32 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)).
Proof.
  intros. rewrite sext_small. f_equal. rewrite signed_of_extract by lia. rewrite rc_le_word4.
  apply rc_swrap_s32. apply rc_u4_range.
Qed.

Lemma rc_lwu : forall b0 b1 b2 b3 : byte,
  zext 64 (bv_extract 0 32 (le_bytes_to_word [b0; b1; b2; b3])) =
  Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
Proof.
  intros. rewrite zext_small. f_equal. rewrite extract_low_mod by lia. rewrite rc_le_word4.
  change (Z.of_N 32) with 32. apply Z.mod_small. apply rc_u4_range.
Qed.

Lemma rc_s32_range : forall u, 0 <= u < 2^32 -> -2^31 <= s32 u < 2^31.
Proof. intros u Hu. unfold s32. destruct (Z.ltb_spec u (2^31)); lia. Qed.

Lemma rc_zxb_eqb : forall (b : byte) z, 0 <= z < 256 -> bv_eqb (zxb b) (Z_to_bv 64 z) = (bv_unsigned b =? z).
Proof.
  intros b z Hz. pose proof (byte_range b). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma rc_byte_eq : forall (b : byte) x, x mod 256 = bv_unsigned b -> Z_to_bv 8 x = b.
Proof.
  intros b x H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. exact H.
Qed.

Lemma rc_le4_bytes : forall b0 b1 b2 b3 : byte,
  [b0; b1; b2; b3] =
  le4 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)).
Proof.
  intros b0 b1 b2 b3.
  pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1.
  pose proof (byte_range b2) as R2. pose proof (byte_range b3) as R3.
  unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia.
  change (2^8) with 256.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]]; symmetry; apply rc_byte_eq; Z.div_mod_to_equations; lia.
Qed.

Lemma rc_sx32 : forall u, 0 <= u < 2^32 -> sx32 (Z_to_bv 64 u) = Z_to_bv 64 (s32 u).
Proof. intros u Hu. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply rc_swrap_s32. exact Hu. Qed.

Lemma rc_zx32 : forall u, 0 <= u < 2^32 -> zx32 (Z_to_bv 64 u) = Z_to_bv 64 u.
Proof. intros u Hu. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. exact Hu. Qed.

Lemma rc_u32le_range : forall row k, 0 <= u32le row k < 2^32.
Proof. intros row k. unfold u32le, rval. apply rc_u4_range. Qed.

Lemma rc_lts0 : forall x, -2^63 <= x < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0) = (x <? 0).
Proof.
  intros x Hx. rewrite bv_lts_zero_r. rewrite unsigned_lit_wrap.
  destruct (Z.ltb_spec x 0).
  - apply Z.leb_le. replace (x mod 2^64) with (x + 2^64); [lia|].
    symmetry. rewrite <- (Z.mod_add x 1 (2^64)) by lia. apply Z.mod_small. lia.
  - apply Z.leb_gt. rewrite Z.mod_small by lia. lia.
Qed.

Lemma rc_land128 : forall b, 0 <= b < 256 -> Z.land b 128 = 128 * (b / 128).
Proof.
  intros b Hb.
  assert (C : forallb (fun b => Z.land b 128 =? 128 * (b / 128)) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. apply Z.eqb_eq. apply C.
  apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.

Lemma rc_land_mask : forall b0 b1 b2 b3 : byte,
  Z.land (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)
    18446744071562067971 = bv_unsigned b0 mod 4 + 2147483648 * (bv_unsigned b3 / 128).
Proof.
  intros b0 b1 b2 b3.
  pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1.
  pose proof (byte_range b2) as R2. pose proof (byte_range b3) as R3.
  rewrite <- (land_mod_pow2_r _ 18446744071562067971 32) by lia.
  change (18446744071562067971 mod 2^32) with (3 + 256 * (0 + 256 * (0 + 256 * 128))).
  replace (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)
    with (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))) by ring.
  rewrite !land_split by lia.
  rewrite !Z.land_0_r. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. rewrite rc_land128 by lia.
  change (2^2) with 4. lia.
Qed.

Lemma rc_eqb_s32 : forall v, 0 <= v < 2^32 -> bv_eqb (Z_to_bv 64 (s32 v)) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite unsigned_lit_wrap. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold s32. destruct (Z.ltb_spec v (2^31)).
  - rewrite Z.mod_small by lia. reflexivity.
  - replace ((v - 2^32) mod 2^64) with (v - 2^32 + 2^64).
    + destruct (Z.eqb_spec v 0); [lia|]. apply Z.eqb_neq. lia.
    + symmetry. rewrite <- (Z.mod_add (v - 2^32) 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma rc_okmask : forall ic u, 0 <= ic < 2^31 -> 0 <= u < 2^32 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64
            (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 u)) 18446744071562067971)))
                   (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 ic)) 3))))) + 0)))
         (Z_to_bv 64 0)
  = (Z.land u 18446744071562067971 =? 0) && (ic mod 4 =? 0).
Proof.
  intros ic u Hic Hu.
  rewrite (unsigned_lit u), (unsigned_lit ic) by lia.
  pose proof (land_lt_pow2 u 18446744071562067971 32 Hu ltac:(lia)) as L1.
  pose proof (land_lt_pow2 ic 3 32 ltac:(lia) ltac:(lia)) as L2.
  rewrite (unsigned_lit (Z.land u _)), (unsigned_lit (Z.land ic _)) by lia.
  pose proof (lor_lt_pow2 _ _ 32 L1 L2) as L3.
  rewrite (unsigned_lit (Z.lor _ _)) by lia. rewrite Z.add_0_r. rewrite rc_swrap_s32 by lia.
  rewrite rc_eqb_s32 by lia.
  change 3 with (Z.ones 2). rewrite (Z.land_ones ic 2) by lia. change (2^2) with 4.
  destruct (Z.eqb_spec (Z.lor (Z.land u 18446744071562067971) (ic mod 4)) 0) as [E|E].
  - apply Z.lor_eq_0_iff in E as [E1 E2]. rewrite E1, E2. reflexivity.
  - symmetry. apply andb_false_iff.
    destruct (Z.eqb_spec (Z.land u 18446744071562067971) 0) as [E1|E1]; [right|left; reflexivity].
    apply Z.eqb_neq. intros E2. apply E. rewrite E1, E2. reflexivity.
Qed.

Lemma rc_srli2 : forall u, 0 <= u < 2^64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 u)) 2 = u / 4.
Proof. intros u Hu. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma rc_srliw2 : forall x, 0 <= x < 2^31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 x))) 2) = x / 4.
Proof.
  intros x Hx. rewrite unsigned_lit by lia. rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 32) with (2^32); lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^2) with 4. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2^31). Z.div_mod_to_equations; lia.
Qed.

Lemma rc_ltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rc_mask_zero : forall row k,
  Z.land (u32le row k) 18446744071562067971 = 0 <-> (u32le row k < 2^31 /\ u32le row k mod 4 = 0).
Proof.
  intros row k. unfold u32le, rval. rewrite rc_land_mask.
  pose proof (byte_range (rbyte row k)) as R0. pose proof (byte_range (rbyte row (k + 1))) as R1.
  pose proof (byte_range (rbyte row (k + 2))) as R2. pose proof (byte_range (rbyte row (k + 3))) as R3.
  split; intros H; Z.div_mod_to_equations; lia.
Qed.

Lemma rc_eqbz : forall x, 0 <= x < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof. intros x Hx. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rc_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rc_addiw_dec : forall x, 1 <= x < 2^31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + -1) = x - 1.
Proof.
  intros x Hx. rewrite unsigned_lit by lia. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.

Lemma rc_seqz_add : forall x, 1 <= x < 2^64 -> x + bv_unsigned (v_sltiu (Z_to_bv 64 x) 1) = x.
Proof.
  intros x Hx. rewrite v_sltiu_b2z. rewrite (unsigned_lit x) by lia. change (bv_wrap 64 1) with 1.
  replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
Qed.

Lemma rc_sextw : forall x, 0 <= x < 2^31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + 0) = x.
Proof.
  intros x Hx. rewrite unsigned_lit by lia. rewrite Z.add_0_r. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2^31). lia.
Qed.

Lemma rc_lts_lit : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed. rewrite !unsigned_lit by lia.
  replace (x <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma rc_swrap32_mod256 : forall x, bv_swrap 32 x mod 256 = x mod 256.
Proof.
  intros x. unfold bv_swrap. change (bv_half_modulus 32) with 2147483648. unfold bv_wrap.
  change (bv_modulus 32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.

Lemma rc_le1_neg : forall s, le1 (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 s)))) =
  [Z_to_bv 8 ((256 - s mod 256) mod 256)].
Proof.
  intros s. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. rewrite mod_mod8_of_modw by lia. change (2^8) with 256.
  rewrite rc_swrap32_mod256. rewrite unsigned_lit_wrap.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rc_zext_sub : forall k, 0 <= k <= 11 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64
    (bv_swrap 32 (11 - bv_unsigned (Z_to_bv 64 k))))) 32))) 32 + 1)) = 12 - k.
Proof.
  intros k Hk. rewrite (unsigned_lit k) by lia.
  rewrite (bv_swrap_small 32 (11 - k)) by (change (bv_half_modulus 32) with (2^31); lia).
  rewrite (unsigned_lit (11 - k)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit ((11 - k) * 2^32)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. rewrite unsigned_lit by lia. lia.
Qed.

Definition runs (lay a b : Z) : list byte :=
  if lay =? 1 then repeat (Z_to_bv 8 1) (Z.to_nat b) ++ repeat (Z_to_bv 8 0) (Z.to_nat a)
  else repeat (Z_to_bv 8 2) (Z.to_nat a) ++ repeat (Z_to_bv 8 1) (Z.to_nat b).

Lemma slot_runs : forall lay a b,
  slot_bytes lay a b = runs lay a b ++ repeat (Z_to_bv 8 3) (Z.to_nat (12 - a - b)).
Proof. intros lay a b. unfold slot_bytes, runs. destruct (lay =? 1); rewrite <- app_assoc; reflexivity. Qed.

Lemma runs_len : forall lay a b, 0 <= a -> 0 <= b -> length (runs lay a b) = Z.to_nat (a + b).
Proof. intros lay a b Ha Hb. unfold runs. destruct (lay =? 1); rewrite length_app, !repeat_length; lia. Qed.

Definition gfacts (row : list byte) (ic oc : Z) : Prop :=
  box_org row <> 0 /\ box_ic row = ic /\ box_oc row = oc /\ 0 <= ic < 2^31 /\ 0 <= oc < 2^31 /\
  ic mod 4 = 0 /\ oc mod 4 = 0 /\ ic / 4 + oc / 4 <= 12.

Lemma head_len : forall row, length (gram_head row) = 8%nat.
Proof. reflexivity. Qed.

Lemma tail_len : forall row, length row = 296%nat -> length (box_tail row) = 11%nat.
Proof. intros row HL. unfold box_tail. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, HL. lia. Qed.

Lemma gfacts_bounds : forall row ic oc, gfacts row ic oc ->
  0 <= ic / 4 /\ 0 <= oc / 4 /\ ic / 4 + oc / 4 <= 12 /\ (ic <> 0 -> 1 <= ic / 4) /\ (oc <> 0 -> 1 <= oc / 4).
Proof.
  intros row ic oc (HO & HI & HOC & Ric & Roc & Mic & Moc & Hab).
  split; [apply Z.div_pos; lia|]. split; [apply Z.div_pos; lia|]. split; [exact Hab|].
  split; intros H; Z.div_mod_to_equations; lia.
Qed.

Lemma gfacts_ok : forall row ic oc, length row = 296%nat -> gfacts row ic oc ->
  decl_ok row = true /\ decl row = gram row /\ length (gram_pre row) = 31%nat /\
  gram_pre row = (gram_head row ++ slot_bytes (box_lay row) (ic / 4) (oc / 4)) ++ firstn 11 (skipn 254 row).
Proof.
  intros row ic oc HLEN G. pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & _).
  destruct G as (HO & HI & HOC & Ric & Roc & Mic & Moc & Hab).
  assert (GO : gram_ok row = true).
  { unfold gram_ok. rewrite HI, HOC.
    repeat (apply andb_true_intro; split); first [apply Z.leb_le; lia | apply Z.eqb_eq; lia]. }
  split. { unfold decl_ok. rewrite GO. apply orb_true_r. }
  split. { unfold decl. rewrite (proj2 (Z.eqb_neq _ _) HO). reflexivity. }
  split.
  - unfold gram_pre. rewrite HI, HOC. rewrite !length_app, head_len, (tail_len row HLEN), slot_runs, length_app,
      runs_len, repeat_length by lia. lia.
  - unfold gram_pre, box_tail. rewrite HI, HOC, app_assoc. reflexivity.
Qed.

Lemma dok_false : forall row, box_org row <> 0 ->
  ~ (0 <= box_ic row /\ 0 <= box_oc row /\ box_ic row mod 4 = 0 /\ box_oc row mod 4 = 0 /\
     box_ic row / 4 + box_oc row / 4 <= 12) -> decl_ok row = false.
Proof.
  intros row HO HN. unfold decl_ok. rewrite (proj2 (Z.eqb_neq _ _) HO). cbn [orb].
  destruct (gram_ok row) eqn:G; [|reflexivity]. exfalso. apply HN. unfold gram_ok in G.
  apply andb_prop in G as [G G5]. apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3].
  apply andb_prop in G as [G1 G2]. apply Z.leb_le in G1, G2, G5. apply Z.eqb_eq in G3, G4. lia.
Qed.

Lemma rc_repeat_snoc : forall (x : byte) n, repeat x n ++ [x] = repeat x (S n).
Proof. intros x n. induction n as [|n IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Section Segs.
Variable segs : list Segment.

Lemma rc_bytes_sub : forall m A bs k n, bytes_at segs m A bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n H Hkn. rewrite <- (CB3_bytes k n bs Hkn) in H.
  apply bytes_at_app in H as [_ H]. apply bytes_at_app in H as [H _].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

Lemma rc_rd4 : forall m A bs k, bytes_at segs m A bs -> (k + 4 <= length bs)%nat ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) 4 = Some (le4 (Z_to_bv 64 (u32le bs k))).
Proof.
  intros m A bs k H Hk. rewrite (bytes_at_read segs m A bs (Z.of_nat k) 4 H) by lia. rewrite Nat2Z.id. f_equal.
  unfold u32le, rval. rewrite <- rc_le4_bytes. unfold rbyte.
  rewrite (rc_firstn_cons bs k 3) by lia. rewrite (rc_firstn_cons bs (S k) 2) by lia.
  rewrite (rc_firstn_cons bs (S (S k)) 1) by lia. rewrite (rc_firstn_cons bs (S (S (S k))) 0) by lia.
  cbn [firstn]. repeat f_equal; lia.
Qed.

Lemma rc_rw_cb : forall m A bs n, bytes_at segs m A bs -> length bs = n -> wr_at segs m A (Z.of_nat n) ->
  rw_cells segs m A [CB n bs].
Proof.
  intros m A bs n HB HL HW. split; [split|].
  - cbn. split; [exact HL | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma rc_cb_rw : forall m A bs n, rw_cells segs m A [CB n bs] ->
  bytes_at segs m A bs /\ length bs = n /\ wr_at segs m A (Z.of_nat n).
Proof.
  intros m A bs n [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as [HL _].
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW. tauto.
Qed.

Lemma rc_wr_sub : forall m A N k n, wr_at segs m A N -> 0 <= k -> 0 <= n -> k + n <= N -> wr_at segs m (A + k) n.
Proof.
  intros m A N k n (H1 & H2 & H) Hk Hn Hkn. split; [lia|]. split; [lia|].
  intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply H. lia.
Qed.

Lemma rc_stk_after : forall m m' lo hi x new,
  stk segs m lo hi -> munch [(x, x + Z.of_nat (length new))] m m' -> wmono segs m m' ->
  bytes_at segs m' x new -> stk segs m' lo hi.
Proof.
  intros m m' lo hi x new (H1 & H2 & H) MU WM HB. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (Z.leb_spec0 x a) as [Hxa|Hxa];
    [destruct (Z.ltb_spec0 a (x + Z.of_nat (length new))) as [Hax|Hax]|].
  - destruct HB as (Hb0 & Hb1 & Hb2).
    specialize (Hb2 (Z.to_nat (a - x)) ltac:(lia)).
    replace (x + Z.of_nat (Z.to_nat (a - x))) with a in Hb2 by lia.
    rewrite Hb2. destruct (nth_error new (Z.to_nat (a - x))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
Qed.

Definition oinv (FB : Z) (FC : list cell) (lo FL FH : Z) (m0 mc : word -> option byte) (M : Z) (row : list byte)
    (O : Z) (P : list byte) : Prop :=
  rw_cells segs mc FB FC /\ stk segs mc lo FB /\ munch [(FL, FH); (O, O + 32)] m0 mc /\ wmono segs m0 mc /\
  mem_inv segs mc /\ bytes_at segs mc M row /\ wr_at segs mc O 32 /\ (length P <= 32)%nat /\
  exists rest, length rest = (32 - length P)%nat /\ bytes_at segs mc O (P ++ rest).

Lemma oinv_init : forall FB FC lo FL FH m0 mc M row O ob,
  rw_cells segs mc FB FC -> stk segs mc lo FB -> munch [(FL, FH); (O, O + 32)] m0 mc -> wmono segs m0 mc ->
  mem_inv segs mc -> bytes_at segs mc M row -> rw_cells segs mc O [CB 32 ob] ->
  oinv FB FC lo FL FH m0 mc M row O [].
Proof.
  intros FB FC lo FL FH m0 mc M row O ob FR ST MU WM MI HR HO.
  destruct (rc_cb_rw mc O ob 32 HO) as (HB & HL & HW).
  do 7 (split; [assumption|]). split; [cbn; lia|].
  exists ob. split; [cbn; lia|]. exact HB.
Qed.

Lemma oinv_ok : forall FB FC lo FL FH m0 mc M row O P k,
  oinv FB FC lo FL FH m0 mc M row O P -> k = Z.of_nat (length P) -> (length P < 32)%nat ->
  store_ok segs mc (wa (O + k)) 1 = true.
Proof.
  intros FB FC lo FL FH m0 mc M row O P k (_ & _ & _ & _ & _ & _ & WR & _) -> Hl.
  apply (wr_at_store_ok segs mc O 32 (Z.of_nat (length P)) 1 WR); lia.
Qed.

Lemma oinv_okw : forall FB FC lo FL FH m0 mc M row O P (x : word),
  oinv FB FC lo FL FH m0 mc M row O P -> bv_unsigned x = O + Z.of_nat (length P) -> (length P < 32)%nat ->
  store_ok segs mc x 1 = true.
Proof.
  intros FB FC lo FL FH m0 mc M row O P x D Hx Hl.
  rewrite <- (wa_of_var x (bv_unsigned x) eq_refl). rewrite Hx.
  eapply oinv_ok; [exact D | reflexivity | exact Hl].
Qed.

Lemma oinv_store : forall FB FC lo FL FH m0 mc M row O P (A v : word) b,
  oinv FB FC lo FL FH m0 mc M row O P -> (length P < 32)%nat ->
  FB + Z.of_nat (cells_size FC) <= O \/ O + 32 <= FB ->
  M + Z.of_nat (length row) <= O \/ O + 32 <= M ->
  A = wa (O + Z.of_nat (length P)) -> le1 v = [b] ->
  oinv FB FC lo FL FH m0 (write_to_mem mc A (le1 v)) M row O (P ++ [b]).
Proof.
  intros FB FC lo FL FH m0 mc M row O P A v b (FR & ST & MU & WM & MI & HR & WR & HL & rest & HLr & HB) Hl DF DR -> Eb.
  rewrite Eb.
  pose proof WR as (HO0 & HO1 & _).
  pose proof (wr_at_store_ok segs mc O 32 (Z.of_nat (length P)) 1 WR ltac:(lia) ltac:(lia)) as HS.
  pose proof (rw_cells_bound segs mc FB FC FR) as FBd.
  pose proof (bytes_at_bound segs mc M row HR) as HRd.
  split. { apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [length]; lia]. }
  split. { apply stk_write; [exact ST | lia | cbn [length]; lia]. }
  split. { apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; right; left; lia]. }
  split. { apply wmono_write. exact WM. }
  split. { apply mem_inv_store; [exact MI | exact HS]. }
  split. { apply bytes_at_write_other; [exact HR | lia | cbn [length]; lia | cbn [length]; lia]. }
  split. { apply wr_at_write. exact WR. }
  split. { rewrite length_app. cbn [length]. lia. }
  destruct rest as [|r rest']; [cbn [length] in HLr; lia|].
  exists rest'. split; [rewrite length_app; cbn [length] in *; lia|].
  rewrite <- app_assoc. cbn [app].
  replace (P ++ b :: rest') with (upd_bytes (P ++ r :: rest') (Z.to_nat (Z.of_nat (length P))) [b]).
  - apply bytes_at_write_inside; [exact HB | lia | rewrite length_app; cbn [length]; lia].
  - unfold upd_bytes. rewrite Nat2Z.id, firstn_app_exact. cbn [length app].
    rewrite skipn_app, skipn_all2 by lia. replace (length P + 1 - length P)%nat with 1%nat by lia. reflexivity.
Qed.

Lemma oinv_call : forall FB FC lo FL FH m0 mc m' M row O P new,
  oinv FB FC lo FL FH m0 mc M row O P -> (length P + length new <= 32)%nat ->
  FB + Z.of_nat (cells_size FC) <= O \/ O + 32 <= FB ->
  M + Z.of_nat (length row) <= O \/ O + 32 <= M ->
  munch [(O + Z.of_nat (length P), O + Z.of_nat (length P) + Z.of_nat (length new))] mc m' ->
  wmono segs mc m' -> mem_inv segs m' -> bytes_at segs m' (O + Z.of_nat (length P)) new ->
  oinv FB FC lo FL FH m0 m' M row O (P ++ new).
Proof.
  intros FB FC lo FL FH m0 mc m' M row O P new (FR & ST & MU & WM & MI & HR & WR & HL & rest & HLr & HB) Hn DF DR
    MUc WMc MIc HN.
  pose proof WR as (HO0 & HO1 & _).
  pose proof (rw_cells_bound segs mc FB FC FR) as FBd.
  split. { eapply rw_cells_transport; [exact FR | exact MUc | exact WMc |]. cbn [disjoint_from]. split; [lia | exact I]. }
  split. { eapply rc_stk_after; [exact ST | exact MUc | exact WMc | exact HN]. }
  split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
    intros z Hz. cbn [outside] in *. destruct Hz as (Hz1 & Hz2 & _). split; [lia | exact I]. }
  split. { eapply wmono_trans; eassumption. }
  split. { exact MIc. }
  split. { eapply bytes_at_transport; [exact HR | exact MUc |]. cbn [disjoint_from]. split; [lia | exact I]. }
  split. { eapply wr_at_transport; eassumption. }
  split. { rewrite length_app. lia. }
  exists (skipn (length new) rest). split. { rewrite length_skipn, length_app. lia. }
  apply bytes_at_app in HB as [HBP HBr].
  rewrite <- app_assoc. apply bytes_at_app. split.
  - eapply bytes_at_transport; [exact HBP | exact MUc |]. cbn [disjoint_from]. split; [lia | exact I].
  - apply bytes_at_app. split; [exact HN|].
    pose proof (rc_bytes_sub mc (O + Z.of_nat (length P)) rest (length new) (length rest - length new) HBr
                  ltac:(lia)) as HS.
    rewrite firstn_all2 in HS by (rewrite length_skipn; lia).
    eapply bytes_at_transport; [exact HS | exact MUc |]. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma oinv_target : forall FB FC lo FL FH m0 mc M row O P n,
  oinv FB FC lo FL FH m0 mc M row O P -> (length P + n <= 32)%nat ->
  exists junk, rw_cells segs mc (O + Z.of_nat (length P)) [CB n junk].
Proof.
  intros FB FC lo FL FH m0 mc M row O P n (_ & _ & _ & _ & _ & _ & WR & HL & rest & HLr & HB) Hn.
  pose proof WR as (HO0 & HO1 & _).
  apply bytes_at_app in HB as [_ HBr].
  pose proof (rc_bytes_sub mc (O + Z.of_nat (length P)) rest 0 n HBr ltac:(lia)) as HS.
  cbn [skipn Z.of_nat] in HS. rewrite Z.add_0_r in HS.
  exists (firstn n rest). apply rc_rw_cb; [exact HS | rewrite firstn_length_le by lia; reflexivity |].
  apply (rc_wr_sub mc O 32); [exact WR | lia | lia | lia].
Qed.

Lemma oinv_rd : forall FB FC lo FL FH m0 mc M row O P i,
  oinv FB FC lo FL FH m0 mc M row O P -> (i < length P)%nat ->
  ov_read_bytes segs mc (wa (O + Z.of_nat i)) 1 = Some [nth i P (Z_to_bv 8 0)].
Proof.
  intros FB FC lo FL FH m0 mc M row O P i (_ & _ & _ & _ & _ & _ & _ & HL & rest & HLr & HB) Hi.
  rewrite (rd_byte segs mc O (P ++ rest) i HB) by (rewrite length_app; lia).
  rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma oinv_row : forall FB FC lo FL FH m0 mc M row O P,
  oinv FB FC lo FL FH m0 mc M row O P -> bytes_at segs mc M row.
Proof. intros FB FC lo FL FH m0 mc M row O P (_ & _ & _ & _ & _ & HR & _). exact HR. Qed.

Lemma oinv_mem_inv : forall FB FC lo FL FH m0 mc M row O P,
  oinv FB FC lo FL FH m0 mc M row O P -> mem_inv segs mc.
Proof. intros FB FC lo FL FH m0 mc M row O P (_ & _ & _ & _ & MI & _). exact MI. Qed.

Lemma oinv_len : forall FB FC lo FL FH m0 mc M row O P,
  oinv FB FC lo FL FH m0 mc M row O P -> (length P <= 32)%nat.
Proof. intros FB FC lo FL FH m0 mc M row O P (_ & _ & _ & _ & _ & _ & _ & HL & _). exact HL. Qed.

Lemma oinv_final : forall FB FC lo FL FH m0 mc M row O P,
  oinv FB FC lo FL FH m0 mc M row O P -> length P = 32%nat ->
  rw_cells segs mc FB FC /\ stk segs mc lo FB /\ munch [(FL, FH); (O, O + 32)] m0 mc /\ wmono segs m0 mc /\
  mem_inv segs mc /\ bytes_at segs mc M row /\ rw_cells segs mc O [CB 32 P].
Proof.
  intros FB FC lo FL FH m0 mc M row O P (FR & ST & MU & WM & MI & HR & WR & HL & rest & HLr & HB) HP.
  do 6 (split; [assumption|]).
  destruct rest as [|r rest]; [|cbn [length] in HLr; lia].
  rewrite app_nil_r in HB. apply rc_rw_cb; [exact HB | exact HP | exact WR].
Qed.

Lemma oinv_bound : forall FB FC lo FL FH m0 mc M row O P,
  oinv FB FC lo FL FH m0 mc M row O P -> 0 <= O /\ O + 32 <= 2^64 /\ (length P <= 32)%nat.
Proof. intros FB FC lo FL FH m0 mc M row O P (_ & _ & _ & _ & _ & _ & (H1 & H2 & _) & HL & _). lia. Qed.

End Segs.
