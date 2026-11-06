From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c.
Import ListNotations.
Open Scope Z_scope.

Definition RF : Z := 1000000000.

Definition gdk (S : list byte) : Z := if fb S 12 =? 0 then -1 else 256 * fb S 13 + fb S 14.

Fixpoint gfind (G M : list byte) (i k : nat) : option nat :=
  match k with
  | O => None
  | Datatypes.S k' => if bytes_eqb (gmac G i) M then Some i else gfind G M (Datatypes.S i) k'
  end.

Definition gedge (G S : list byte) (i : nat) : bool :=
  (negb (fu S 8 4 =? 0) && negb (fu S 8 4 =? fu G (32 * i + 8) 4))
  || ((0 <=? gdk S) && negb (gdk S =? s32 (fu G (32 * i + 12) 4)))
  || (negb (fb S 16 =? 0) && negb (fb S 16 =? fb G (32 * i + 16))).

Definition gate_model (G S : list byte) (now : Z) : list byte * Z :=
  match gfind G (fld S 0 6) 0 (Z.to_nat (gn G)) with
  | Some i =>
      if gedge G S i then
        let G1 := if fu S 8 4 =? 0 then G else upd_bytes G (32 * i + 8) (fld S 8 4) in
        let G2 := if fb S 16 =? 0 then G1 else upd_bytes G1 (32 * i + 16) [nth 16 S (zb 0)] in
        let G3 := if gdk S <? 0 then G2 else upd_bytes G2 (32 * i + 12) (le4 (Z_to_bv 64 (gdk S))) in
        (upd_bytes G3 (32 * i + 24) (le8 (Z_to_bv 64 now)), 1)
      else if (now <? fu G (32 * i + 24) 8) || (RF <=? now - fu G (32 * i + 24) 8) then
        (upd_bytes G (32 * i + 24) (le8 (Z_to_bv 64 now)), 1)
      else (G, 0)
  | None =>
      if 8 <=? gn G then (G, 0)
      else
        let e := (32 * Z.to_nat (gn G))%nat in
        let G1 := upd_bytes G 256 (le4 (Z_to_bv 64 (gn G + 1))) in
        let G2 := upd_bytes G1 e (fld S 0 6) in
        let G3 := upd_bytes G2 (e + 8) (fld S 8 4) in
        let G4 := upd_bytes G3 (e + 12) (le4 (Z_to_bv 64 (gdk S))) in
        let G5 := upd_bytes G4 (e + 16) [nth 16 S (zb 0)] in
        (upd_bytes G5 (e + 24) (le8 (Z_to_bv 64 now)), 1)
  end.

Lemma nth_error_firstn_g : forall {X} (l : list X) n j,
  nth_error (firstn n l) j = if (j <? n)%nat then nth_error l j else None.
Proof.
  intros X l. induction l as [|x l IH]; intros n j.
  - rewrite firstn_nil. destruct (j <? n)%nat; destruct j; reflexivity.
  - destruct n as [|n]; [destruct j; reflexivity|].
    destruct j as [|j]; [reflexivity|]. cbn [firstn nth_error]. rewrite IH. reflexivity.
Qed.

Lemma nth_error_skipn_g : forall {X} (l : list X) k j, nth_error (skipn k l) j = nth_error l (k + j).
Proof.
  intros X l k. revert l. induction k as [|k IH]; intros [|x l] j; cbn; try reflexivity.
  - destruct j; reflexivity.
  - apply IH.
Qed.

Lemma nth_error_fld : forall (B : list byte) k n j,
  nth_error (fld B k n) j = if (j <? n)%nat then nth_error B (k + j) else None.
Proof. intros. unfold fld. rewrite nth_error_firstn_g, nth_error_skipn_g. reflexivity. Qed.

Lemma length_fld : forall (B : list byte) k n, (k + n <= length B)%nat -> length (fld B k n) = n.
Proof. intros. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma nth_error_upd : forall (cs : list byte) k bs, (k + length bs <= length cs)%nat -> forall i,
  nth_error (upd_bytes cs k bs) i =
    if ((k <=? i) && (i <? k + length bs))%nat then nth_error bs (i - k) else nth_error cs i.
Proof.
  intros cs k bs H i. destruct (Nat.lt_ge_cases i (length cs)) as [Hi|Hi].
  - apply upd_bytes_nth; assumption.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite upd_bytes_length; lia).
    destruct (Nat.leb_spec k i), (Nat.ltb_spec i (k + length bs)); cbn [andb]; try lia;
      symmetry; apply nth_error_None; lia.
Qed.

Lemma fld_upd_other : forall (B : list byte) p X k n,
  (p + length X <= length B)%nat -> (k + n <= p \/ p + length X <= k)%nat ->
  fld (upd_bytes B p X) k n = fld B k n.
Proof.
  intros B p X k n H Hd. apply nth_error_ext. intros j. rewrite !nth_error_fld.
  destruct (Nat.ltb_spec j n); [|reflexivity]. rewrite nth_error_upd by exact H.
  destruct (Nat.leb_spec p (k + j)), (Nat.ltb_spec (k + j) (p + length X)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma fld_upd_same : forall (B : list byte) p X,
  (p + length X <= length B)%nat -> fld (upd_bytes B p X) p (length X) = X.
Proof.
  intros B p X H. apply nth_error_ext. intros j. rewrite nth_error_fld.
  destruct (Nat.ltb_spec j (length X)).
  - rewrite nth_error_upd by exact H.
    destruct (Nat.leb_spec p (p + j)), (Nat.ltb_spec (p + j) (p + length X)); cbn [andb]; try lia.
    f_equal. lia.
  - symmetry. apply nth_error_None. lia.
Qed.

Lemma upd_comm : forall (B : list byte) k1 X1 k2 X2,
  (k1 + length X1 <= length B)%nat -> (k2 + length X2 <= length B)%nat ->
  (k1 + length X1 <= k2 \/ k2 + length X2 <= k1)%nat ->
  upd_bytes (upd_bytes B k1 X1) k2 X2 = upd_bytes (upd_bytes B k2 X2) k1 X1.
Proof.
  intros B k1 X1 k2 X2 H1 H2 Hd. apply nth_error_ext. intros j.
  rewrite (nth_error_upd (upd_bytes B k1 X1)) by (rewrite upd_bytes_length; lia).
  rewrite (nth_error_upd (upd_bytes B k2 X2)) by (rewrite upd_bytes_length; lia).
  rewrite !nth_error_upd by lia.
  destruct (Nat.leb_spec k1 j), (Nat.ltb_spec j (k1 + length X1)), (Nat.leb_spec k2 j),
    (Nat.ltb_spec j (k2 + length X2)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma upd_adj : forall (B : list byte) p Y X,
  (p + length Y + length X <= length B)%nat ->
  upd_bytes (upd_bytes B (p + length Y) X) p Y = upd_bytes B p (Y ++ X).
Proof.
  intros B p Y X H. apply nth_error_ext. intros j.
  rewrite (nth_error_upd (upd_bytes B (p + length Y) X)) by (rewrite upd_bytes_length; lia).
  rewrite !nth_error_upd by (rewrite ?length_app; lia). rewrite length_app.
  destruct (Nat.leb_spec p j), (Nat.ltb_spec j (p + length Y)), (Nat.leb_spec (p + length Y) j),
    (Nat.ltb_spec j (p + length Y + length X)), (Nat.ltb_spec j (p + (length Y + length X)));
    cbn [andb]; try reflexivity; try lia.
  - rewrite nth_error_app1 by lia. reflexivity.
  - rewrite nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma fld_app_06 : forall S : list byte, (6 <= length S)%nat -> fld S 0 4 ++ fld S 4 2 = fld S 0 6.
Proof.
  intros S H. apply nth_error_ext. intros j.
  destruct (Nat.lt_ge_cases j 4).
  - rewrite nth_error_app1 by (rewrite length_fld; lia). rewrite !nth_error_fld.
    destruct (Nat.ltb_spec j 4), (Nat.ltb_spec j 6); try lia. reflexivity.
  - rewrite nth_error_app2 by (rewrite length_fld; lia). rewrite length_fld by lia. rewrite !nth_error_fld.
    destruct (Nat.ltb_spec (j - 4) 2), (Nat.ltb_spec j 6); try lia; [f_equal; lia | reflexivity].
Qed.

Lemma fld1 : forall (B : list byte) k, (k < length B)%nat -> fld B k 1 = [nth k B (zb 0)].
Proof.
  intros B k H. apply nth_error_ext. intros j. rewrite nth_error_fld.
  destruct j as [|j]; cbn [Nat.ltb Nat.leb nth_error].
  - rewrite Nat.add_0_r. apply nth_error_nth'. exact H.
  - destruct j; reflexivity.
Qed.

Lemma gfind_None : forall G M k i, gfind G M i k = None ->
  forall j, (i <= j < i + k)%nat -> bytes_eqb (gmac G j) M = false.
Proof.
  intros G M k. induction k as [|k IH]; intros i H j Hj; [lia|].
  cbn [gfind] in H. destruct (bytes_eqb (gmac G i) M) eqn:E; rewrite ?E in H; cbv beta iota in H; [discriminate|].
  destruct (Nat.eq_dec j i) as [->|NE]; [exact E|]. apply (IH (Datatypes.S i) H). lia.
Qed.

Lemma gfind_Some : forall G M k i j, gfind G M i k = Some j ->
  (i <= j < i + k)%nat /\ bytes_eqb (gmac G j) M = true.
Proof.
  intros G M k. induction k as [|k IH]; intros i j H; [discriminate|].
  cbn [gfind] in H. destruct (bytes_eqb (gmac G i) M) eqn:E; rewrite ?E in H; cbv beta iota in H.
  - injection H as <-. split; [lia | exact E].
  - destruct (IH (Datatypes.S i) j H) as [R B]. split; [lia | exact B].
Qed.

Lemma gfind_None_intro : forall G M k i,
  (forall j, (i <= j < i + k)%nat -> bytes_eqb (gmac G j) M = false) -> gfind G M i k = None.
Proof.
  intros G M k. induction k as [|k IH]; intros i H; [reflexivity|].
  cbn [gfind]. rewrite (H i) by lia. cbv beta iota. apply IH. intros j Hj. apply H. lia.
Qed.

Lemma gfind_Some_intro : forall G M k i j, (i <= j < i + k)%nat ->
  (forall j', (i <= j' < j)%nat -> bytes_eqb (gmac G j') M = false) ->
  bytes_eqb (gmac G j) M = true -> gfind G M i k = Some j.
Proof.
  intros G M k. induction k as [|k IH]; intros i j Hj Hb Hm; [lia|].
  cbn [gfind]. destruct (Nat.eq_dec i j) as [->|NE]; [rewrite Hm; reflexivity|].
  rewrite (Hb i) by lia. cbv beta iota. apply IH; [lia | | exact Hm]. intros j' Hj'. apply Hb. lia.
Qed.

Definition keeps (B B' : list byte) : Prop :=
  length B' = length B /\ gn B' = gn B /\ forall j, (j < 8)%nat -> gmac B' j = gmac B j.

Lemma keeps_refl : forall B, keeps B B.
Proof. intros B. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. Qed.

Lemma keeps_trans : forall B1 B2 B3, keeps B1 B2 -> keeps B2 B3 -> keeps B1 B3.
Proof.
  intros B1 B2 B3 (L1 & N1 & M1) (L2 & N2 & M2). split; [lia|]. split; [congruence|].
  intros j Hj. rewrite M2, M1 by exact Hj. reflexivity.
Qed.

Lemma keeps_ok : forall B B', gate_ok B -> keeps B B' -> gate_ok B'.
Proof.
  intros B B' (HL & Hn & HD) (L & N & M). unfold gate_ok. split; [lia|]. rewrite N. split; [lia|].
  intros i j Hij Hj. rewrite !M by lia. apply HD; lia.
Qed.

Lemma keeps_upd : forall B p X, length B = 264%nat -> (p + length X <= 256)%nat ->
  (forall j, (j < 8)%nat -> (32 * j + 6 <= p \/ p + length X <= 32 * j)%nat) ->
  keeps B (upd_bytes B p X).
Proof.
  intros B p X HL Hp Hj. split; [apply upd_bytes_length; lia|]. split.
  - unfold gn, fu. rewrite fld_upd_other by lia. reflexivity.
  - intros j Hj8. unfold gmac. apply fld_upd_other; [lia|]. specialize (Hj j Hj8). lia.
Qed.

Lemma keeps_entry : forall B i c X, length B = 264%nat -> (i < 8)%nat -> (8 <= c)%nat ->
  (c + length X <= 32)%nat -> keeps B (upd_bytes B (32 * i + c) X).
Proof. intros B i c X HL Hi Hc HX. apply keeps_upd; [exact HL | lia | intros j Hj; lia]. Qed.

Lemma keeps_entry_opt : forall (b : bool) B i c X, length B = 264%nat -> (i < 8)%nat -> (8 <= c)%nat ->
  (c + length X <= 32)%nat -> keeps B (if b then B else upd_bytes B (32 * i + c) X).
Proof. intros [|] B i c X HL Hi Hc HX; [apply keeps_refl | apply keeps_entry; assumption]. Qed.

Lemma length_upd : forall (B : list byte) p X, (p + length X <= length B)%nat -> length (upd_bytes B p X) = length B.
Proof. intros. apply upd_bytes_length. exact H. Qed.

Lemma ble_range : forall w : list byte, 0 <= bytes_le_to_Z w < 256 ^ Z.of_nat (length w).
Proof.
  intros w. rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map w)) as R.
  rewrite length_map in R. exact R.
Qed.

Lemma ble4_range : forall w : list byte, length w = 4%nat -> 0 <= bytes_le_to_Z w < 2 ^ 32.
Proof. intros w H. pose proof (ble_range w) as R. rewrite H in R. exact R. Qed.

Lemma ble8_range : forall w : list byte, length w = 8%nat -> 0 <= bytes_le_to_Z w < 2 ^ 64.
Proof. intros w H. pose proof (ble_range w) as R. rewrite H in R. exact R. Qed.

Lemma s32_swrap : forall x, 0 <= x < 2 ^ 32 -> bv_swrap 32 x = s32 x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, s32. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). destruct (Z.ltb_spec x (2 ^ 31)); Z.div_mod_to_equations; lia.
Qed.

Lemma s32_range : forall x, 0 <= x < 2 ^ 32 -> - 2 ^ 31 <= s32 x < 2 ^ 31.
Proof. intros x Hx. unfold s32. destruct (Z.ltb_spec x (2 ^ 31)); lia. Qed.

Lemma s32_inj : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> (s32 x =? s32 y) = (x =? y).
Proof.
  intros x y Hx Hy. destruct (Z.eqb_spec x y) as [->|NE]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. unfold s32. destruct (Z.ltb_spec x (2 ^ 31)), (Z.ltb_spec y (2 ^ 31)); lia.
Qed.

Lemma s32_small : forall x, 0 <= x < 2 ^ 31 -> s32 x = x.
Proof. intros x Hx. unfold s32. destruct (Z.ltb_spec x (2 ^ 31)); lia. Qed.

Lemma lw_val : forall w : list byte, length w = 4%nat ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word w)) = Z_to_bv 64 (s32 (bytes_le_to_Z w)).
Proof.
  intros w Hl. rewrite sext_small, signed_of_extract by lia. f_equal.
  pose proof (ble4_range w Hl) as R. unfold le_bytes_to_word. rewrite unsigned_lit by lia.
  apply s32_swrap. exact R.
Qed.

Lemma ld_val : forall w : list byte, length w = 8%nat ->
  bv_extract 0 64 (le_bytes_to_word w) = Z_to_bv 64 (bytes_le_to_Z w).
Proof.
  intros w Hl. apply bv_eq. rewrite load8_le_val by exact Hl. rewrite <- bytes_le_to_Z_le_val.
  pose proof (ble8_range w Hl). rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma ble_inv : forall w : list byte, Z_to_le_bytes (length w) (bytes_le_to_Z w) = w.
Proof.
  induction w as [|b w IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_rng b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z w) by apply (proj1 (ble_range w)).
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z w) with (bv_unsigned b + bytes_le_to_Z w * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z w) with (bv_unsigned b + bytes_le_to_Z w * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma le_ext_mod : forall k (w : list byte) z, length w = k -> (8 * Z.of_nat k <= 64)%Z ->
  z mod 2 ^ (8 * Z.of_nat k) = bytes_le_to_Z w -> Z_to_le_bytes k z = w.
Proof.
  intros k w z Hl Hk Hz. rewrite <- (Z_to_le_bytes_mod k z (8 * Z.of_nat k)) by lia.
  rewrite Hz, <- Hl. apply ble_inv.
Qed.

Lemma le4_lw_g : forall w : list byte, length w = 4%nat -> le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word w))) = w.
Proof.
  intros w Hl. rewrite lw_val by exact Hl. unfold le4. apply le_ext_mod; [exact Hl | lia |].
  change (8 * Z.of_nat 4) with 32. pose proof (ble4_range w Hl) as R.
  rewrite unsigned_lit_wrap. unfold s32.
  destruct (Z.ltb_spec (bytes_le_to_Z w) (2 ^ 31)); Z.div_mod_to_equations; lia.
Qed.

Lemma le2_lh_g : forall w : list byte, length w = 2%nat -> le2 (sext 64 (bv_extract 0 16 (le_bytes_to_word w))) = w.
Proof.
  intros w Hl. rewrite sext_small, signed_of_extract by lia. unfold le2.
  apply le_ext_mod; [exact Hl | lia |]. change (8 * Z.of_nat 2) with 16.
  pose proof (ble_range w) as R. rewrite Hl in R. change (256 ^ Z.of_nat 2) with (2 ^ 16) in R.
  unfold le_bytes_to_word. rewrite (unsigned_lit (bytes_le_to_Z w)) by lia.
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 16) with (2 ^ 15). change (bv_modulus 16) with (2 ^ 16).
  Z.div_mod_to_equations. lia.
Qed.

Lemma le4_s32_ble : forall w : list byte, length w = 4%nat -> le4 (Z_to_bv 64 (s32 (bytes_le_to_Z w))) = w.
Proof. intros w Hl. rewrite <- lw_val by exact Hl. apply le4_lw_g. exact Hl. Qed.

Lemma s32_le4 : forall v, 0 <= v < 2 ^ 31 -> s32 (bytes_le_to_Z (le4 (Z_to_bv 64 v))) = v.
Proof.
  intros v Hv. rewrite bytes_le_to_Z_le4, unsigned_lit by lia. rewrite Z.mod_small by lia.
  apply s32_small. exact Hv.
Qed.

Lemma signed_lit : forall a, - 2 ^ 63 <= a < 2 ^ 63 -> bv_signed (Z_to_bv 64 a) = a.
Proof.
  intros a Ha. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.ltb_spec (a mod 2 ^ 64) (2 ^ 63)); Z.div_mod_to_equations; lia.
Qed.

Lemma eqb_lit : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec a b) as [->|NE]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply NE. Z.div_mod_to_equations. lia.
Qed.

Lemma lts_lit : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_lts. rewrite !signed_lit by assumption. reflexivity. Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma zxb_lit : forall b : byte, zxb b = Z_to_bv 64 (bv_unsigned b).
Proof. reflexivity. Qed.

Lemma fb_rng : forall B k, 0 <= fb B k < 256.
Proof. intros. apply byte_rng. Qed.

Lemma gdk_rng : forall S, -1 <= gdk S < 65536.
Proof.
  intros S. unfold gdk. pose proof (fb_rng S 13). pose proof (fb_rng S 14).
  destruct (fb S 12 =? 0); lia.
Qed.

Lemma s32_eq0 : forall x, 0 <= x < 2 ^ 32 -> (s32 x =? 0) = (x =? 0).
Proof.
  intros x Hx. unfold s32. destruct (Z.ltb_spec x (2 ^ 31)); [reflexivity|].
  destruct (Z.eqb_spec (x - 2 ^ 32) 0), (Z.eqb_spec x 0); try reflexivity; lia.
Qed.

Lemma le4_s32_fu : forall B k, (k + 4 <= length B)%nat -> le4 (Z_to_bv 64 (s32 (fu B k 4))) = fld B k 4.
Proof. intros B k H. unfold fu. apply le4_s32_ble. apply length_fld. exact H. Qed.

Lemma le1_fb : forall B k, le1 (Z_to_bv 64 (fb B k)) = [nth k B (zb 0)].
Proof. intros B k. unfold fb. apply le1_zxb. Qed.

Definition hide (P : Prop) : Prop := P.
Lemma hide_intro : forall P : Prop, P -> hide P.
Proof. intros P H. exact H. Qed.

Lemma rw_CB_bytes : forall segs m A n B, rw_cells segs m A [CB n B] -> bytes_at segs m A B /\ length B = n.
Proof.
  intros segs m A n B [[[Hl _] Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  split; [exact Hb | exact Hl].
Qed.

Lemma rw_CB_read : forall segs m A n B k j, rw_cells segs m A [CB n B] -> (k + j <= n)%nat ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) j = Some (fld B k j).
Proof.
  intros segs m A n B k j H Hk. destruct (rw_CB_bytes _ _ _ _ _ H) as [Hb Hl].
  apply bytes_at_ov_read; [exact Hb | lia].
Qed.

Lemma rw_CB_store_ok : forall segs m A n B k j, rw_cells segs m A [CB n B] -> (k + j <= n)%nat ->
  store_ok segs m (wa (A + Z.of_nat k)) j = true.
Proof.
  intros segs m A n B k j [_ Hw] Hk.
  apply (wr_at_store_ok segs m A (Z.of_nat (cells_size [CB n B]))); [exact Hw | lia | cbn [cells_size csize]; lia].
Qed.

Lemma rw_CB_write : forall segs m A n B k bs, rw_cells segs m A [CB n B] -> (k + length bs <= n)%nat ->
  rw_cells segs (write_to_mem m (wa (A + Z.of_nat k)) bs) A [CB n (upd_bytes B k bs)].
Proof.
  intros segs m A n B k bs H Hk. destruct (rw_CB_bytes _ _ _ _ _ H) as [Hb Hl]. destruct H as [_ Hw].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (bytes_at_write_inside segs m A B (Z.of_nat k) bs Hb ltac:(lia) ltac:(lia)) as E.
    rewrite Nat2Z.id in E. exact E.
  - apply wr_at_write. exact Hw.
Qed.

Lemma bytes_read_fld : forall segs m A B k j, bytes_at segs m A B -> (k + j <= length B)%nat ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) j = Some (fld B k j).
Proof. intros. apply bytes_at_ov_read; assumption. Qed.

Lemma bytes_at_fld : forall segs m A B k n, bytes_at segs m A B -> (k + n <= length B)%nat ->
  bytes_at segs m (A + Z.of_nat k) (fld B k n).
Proof.
  intros segs m A B k n H Hk. unfold fld.
  rewrite <- (firstn_skipn k B) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length B)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k B)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma bat_word : forall segs m A A' bs, bytes_at segs m A bs -> A' = A -> A < 2 ^ 64 ->
  bytes_at segs m (bv_unsigned (Z_to_bv 64 A')) bs.
Proof.
  intros segs m A A' bs H -> HA. pose proof (bytes_at_bound segs m A bs H) as B.
  rewrite unsigned_lit by lia. exact H.
Qed.

Lemma gm_edge : forall G S now i, gfind G (fld S 0 6) 0 (Z.to_nat (gn G)) = Some i -> gedge G S i = true ->
  gate_model G S now =
    (upd_bytes (if gdk S <? 0
                then (if fb S 16 =? 0 then (if fu S 8 4 =? 0 then G else upd_bytes G (32 * i + 8) (fld S 8 4))
                      else upd_bytes (if fu S 8 4 =? 0 then G else upd_bytes G (32 * i + 8) (fld S 8 4))
                             (32 * i + 16) [nth 16 S (zb 0)])
                else upd_bytes (if fb S 16 =? 0 then (if fu S 8 4 =? 0 then G else upd_bytes G (32 * i + 8) (fld S 8 4))
                                else upd_bytes (if fu S 8 4 =? 0 then G else upd_bytes G (32 * i + 8) (fld S 8 4))
                                       (32 * i + 16) [nth 16 S (zb 0)])
                       (32 * i + 12) (le4 (Z_to_bv 64 (gdk S))))
       (32 * i + 24) (le8 (Z_to_bv 64 now)), 1).
Proof. intros G S now i H1 H2. unfold gate_model. rewrite H1. cbv beta iota. rewrite H2. reflexivity. Qed.

Lemma gm_refresh : forall G S now i, gfind G (fld S 0 6) 0 (Z.to_nat (gn G)) = Some i -> gedge G S i = false ->
  (now <? fu G (32 * i + 24) 8) || (RF <=? now - fu G (32 * i + 24) 8) = true ->
  gate_model G S now = (upd_bytes G (32 * i + 24) (le8 (Z_to_bv 64 now)), 1).
Proof. intros G S now i H1 H2 H3. unfold gate_model. rewrite H1. cbv beta iota. rewrite H2, H3. reflexivity. Qed.

Lemma gm_keep : forall G S now i, gfind G (fld S 0 6) 0 (Z.to_nat (gn G)) = Some i -> gedge G S i = false ->
  (now <? fu G (32 * i + 24) 8) || (RF <=? now - fu G (32 * i + 24) 8) = false ->
  gate_model G S now = (G, 0).
Proof. intros G S now i H1 H2 H3. unfold gate_model. rewrite H1. cbv beta iota. rewrite H2, H3. reflexivity. Qed.

Lemma gm_full : forall G S now, gfind G (fld S 0 6) 0 (Z.to_nat (gn G)) = None -> 8 <= gn G ->
  gate_model G S now = (G, 0).
Proof.
  intros G S now H1 H2. unfold gate_model. rewrite H1. cbv beta iota.
  destruct (Z.leb_spec 8 (gn G)); [reflexivity | lia].
Qed.

Lemma gm_app : forall G S now N, gfind G (fld S 0 6) 0 (Z.to_nat (gn G)) = None -> gn G = Z.of_nat N -> (N < 8)%nat ->
  gate_model G S now =
    (upd_bytes (upd_bytes (upd_bytes (upd_bytes (upd_bytes (upd_bytes G 256 (le4 (Z_to_bv 64 (Z.of_nat N + 1))))
       (32 * N) (fld S 0 6)) (32 * N + 8) (fld S 8 4)) (32 * N + 12) (le4 (Z_to_bv 64 (gdk S))))
       (32 * N + 16) [nth 16 S (zb 0)]) (32 * N + 24) (le8 (Z_to_bv 64 now)), 1).
Proof.
  intros G S now N H1 H2 H3. unfold gate_model. rewrite H1. cbv beta iota. destruct (Z.leb_spec 8 (gn G)); [lia|].
  rewrite H2, Nat2Z.id. reflexivity.
Qed.

Lemma fu_rng4 : forall B k, (k + 4 <= length B)%nat -> 0 <= fu B k 4 < 2 ^ 32.
Proof. intros B k H. unfold fu. apply ble4_range. apply length_fld. exact H. Qed.

Lemma fu_rng8 : forall B k, (k + 8 <= length B)%nat -> 0 <= fu B k 8 < 2 ^ 64.
Proof. intros B k H. unfold fu. apply ble8_range. apply length_fld. exact H. Qed.

Lemma gn_upd_n : forall G v, length G = 264%nat -> 0 <= v < 2 ^ 31 ->
  gn (upd_bytes G 256 (le4 (Z_to_bv 64 v))) = v.
Proof.
  intros G v HL Hv. unfold gn, fu.
  pose proof (fld_upd_same G 256 (le4 (Z_to_bv 64 v))) as E. rewrite length_le4 in E.
  rewrite E by lia. apply s32_le4. exact Hv.
Qed.

Lemma gate_model_ok : forall G S now, gate_ok G -> length S = 24%nat -> gate_ok (fst (gate_model G S now)).
Proof.
  intros G S now HG HS. pose proof HG as (HL & Hn & HD).
  unfold gate_model.
  destruct (gfind G (fld S 0 6) 0 (Z.to_nat (gn G))) as [i|] eqn:F.
  - destruct (gfind_Some _ _ _ _ _ F) as [Ri _].
    assert (Hi : (i < 8)%nat) by lia.
    assert (L8 : length (le8 (Z_to_bv 64 now)) = 8%nat) by apply length_le8.
    destruct (gedge G S i).
    + cbv zeta. cbn [fst]. apply (keeps_ok G); [exact HG|].
      set (G1 := if fu S 8 4 =? 0 then G else upd_bytes G (32 * i + 8) (fld S 8 4)).
      assert (K1 : keeps G G1) by (apply keeps_entry_opt; [exact HL | exact Hi | lia | rewrite length_fld; lia]).
      set (G2 := if fb S 16 =? 0 then G1 else upd_bytes G1 (32 * i + 16) [nth 16 S (zb 0)]).
      assert (K2 : keeps G1 G2) by (apply keeps_entry_opt; [destruct K1 as [L _]; lia | exact Hi | lia | cbn; lia]).
      set (G3 := if gdk S <? 0 then G2 else upd_bytes G2 (32 * i + 12) (le4 (Z_to_bv 64 (gdk S)))).
      assert (K3 : keeps G2 G3)
        by (apply keeps_entry_opt; [destruct K1 as [L _]; destruct K2 as [L' _]; lia | exact Hi | lia | rewrite length_le4; lia]).
      apply (keeps_trans G G3); [apply (keeps_trans G G2); [apply (keeps_trans G G1)|]|]; try assumption.
      apply keeps_entry; [destruct K1 as [L _]; destruct K2 as [L' _]; destruct K3 as [L'' _]; lia | exact Hi | lia | lia].
    + destruct ((now <? fu G (32 * i + 24) 8) || (RF <=? now - fu G (32 * i + 24) 8)); cbn [fst]; [|exact HG].
      apply (keeps_ok G); [exact HG|]. apply keeps_entry; [exact HL | exact Hi | lia | lia].
  - destruct (Z.leb_spec 8 (gn G)); cbn [fst]; [exact HG|]. cbv zeta.
    set (N := Z.to_nat (gn G)).
    assert (EN : Z.of_nat N = gn G) by (unfold N; lia).
    set (G1 := upd_bytes G 256 (le4 (Z_to_bv 64 (gn G + 1)))).
    assert (L1 : length G1 = 264%nat) by (unfold G1; rewrite length_upd; rewrite ?length_le4; lia).
    assert (N1 : gn G1 = gn G + 1) by (apply gn_upd_n; lia).
    assert (M1 : forall j, (j < 8)%nat -> gmac G1 j = gmac G j)
      by (intros j Hj; unfold G1, gmac; apply fld_upd_other; rewrite ?length_le4; lia).
    set (G2 := upd_bytes G1 (32 * N) (fld S 0 6)).
    assert (L6 : length (fld S 0 6) = 6%nat) by (apply length_fld; lia).
    assert (L2 : length G2 = 264%nat) by (unfold G2; rewrite length_upd; lia).
    assert (N2 : gn G2 = gn G + 1) by (unfold G2, gn, fu; rewrite fld_upd_other by lia; exact N1).
    assert (M2 : forall j, (j < N)%nat -> gmac G2 j = gmac G j)
      by (intros j Hj; unfold G2, gmac; rewrite fld_upd_other by lia; apply M1; lia).
    assert (M2n : gmac G2 N = fld S 0 6).
    { unfold G2, gmac. pose proof (fld_upd_same G1 (32 * N) (fld S 0 6)) as E. rewrite L6 in E. apply E. lia. }
    assert (K : keeps G2 (upd_bytes (upd_bytes (upd_bytes (upd_bytes G2 (32 * N + 8) (fld S 8 4))
                   (32 * N + 12) (le4 (Z_to_bv 64 (gdk S)))) (32 * N + 16) [nth 16 S (zb 0)])
                   (32 * N + 24) (le8 (Z_to_bv 64 now)))).
    { assert (Hi : (N < 8)%nat) by lia.
      assert (K3 : keeps G2 (upd_bytes G2 (32 * N + 8) (fld S 8 4)))
        by (apply keeps_entry; [exact L2 | exact Hi | lia | rewrite length_fld; lia]).
      assert (K4 : keeps G2 (upd_bytes (upd_bytes G2 (32 * N + 8) (fld S 8 4)) (32 * N + 12) (le4 (Z_to_bv 64 (gdk S))))).
      { apply (keeps_trans _ _ _ K3). apply keeps_entry; [destruct K3 as [L _]; lia | exact Hi | lia | rewrite length_le4; lia]. }
      assert (K5 : keeps G2 (upd_bytes (upd_bytes (upd_bytes G2 (32 * N + 8) (fld S 8 4)) (32 * N + 12)
                     (le4 (Z_to_bv 64 (gdk S)))) (32 * N + 16) [nth 16 S (zb 0)])).
      { apply (keeps_trans _ _ _ K4). apply keeps_entry; [destruct K4 as [L _]; lia | exact Hi | lia | cbn; lia]. }
      apply (keeps_trans _ _ _ K5). apply keeps_entry; [destruct K5 as [L _]; lia | exact Hi | lia | rewrite length_le8; lia]. }
    destruct K as (LK & NK & MK).
    unfold gate_ok. split; [lia|]. rewrite NK, N2. split; [lia|].
    intros i j Hij Hj. rewrite !MK by lia.
    destruct (Nat.eq_dec j N) as [->|NE].
    + rewrite M2n, M2 by lia. apply (gfind_None _ _ _ _ F). lia.
    + rewrite !M2 by lia. apply HD; lia.
Qed.

Ltac gst HG HST k :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
    lazymatch type of HG with
    | hide (rw_cells segs mm ?A [CB ?n ?B]) =>
      replace (write_to_mem mm a bs) with (write_to_mem mm (wa (A + Z.of_nat k)) bs)
        by (f_equal; unfold wa; f_equal; lia);
      unfold hide in HG;
      lazymatch goal with
      | MI : mem_inv segs mm |- _ =>
          apply (mem_inv_store segs mm (wa (A + Z.of_nat k)) bs) in MI;
          [ | apply (rw_CB_store_ok segs mm A n B k (length bs) HG); simpl_sizes; lia ]
      end;
      apply (rw_CB_write segs mm A n B k bs) in HG; [ | simpl_sizes; lia ];
      clear HST;
      transport_chunks segs mm (A + Z.of_nat k)%Z bs;
      footprint_after_store segs mm (A + Z.of_nat k)%Z bs;
      let m' := fresh "m" in
      remember (write_to_mem mm (wa (A + Z.of_nat k)) bs) as m' eqn:Heqm;
      clear Heqm; try clear mm
    end
  end.

Ltac gstep_st HG k j :=
  lazymatch type of HG with
  | rw_cells ?segs ?mm ?A [CB ?n ?B] =>
    let HST := fresh "HST" in
    pose proof (rw_CB_store_ok segs mm A n B k j HG ltac:(lia)) as HST;
    apply hide_intro in HG; step; gst HG HST k
  end.

Ltac gld HG k j :=
  lazymatch type of HG with
  | rw_cells ?segs ?mm ?A [CB ?n ?B] =>
    let HR := fresh "HR" in
    pose proof (rw_CB_read segs mm A n B k j HG ltac:(lia)) as HR;
    try rewrite fld1 in HR by lia;
    apply hide_intro in HG; step; unfold hide in HG; clear HR
  end.

Ltac sld HS k j :=
  lazymatch type of HS with
  | bytes_at ?segs ?mm ?A ?B =>
    let HR := fresh "HR" in
    pose proof (bytes_read_fld segs mm A B k j HS ltac:(lia)) as HR;
    try rewrite fld1 in HR by lia;
    step; clear HR
  end.

Lemma app_eq : forall (B X0 X1 X2 X3 X4 X5 : list byte) p, length B = 264%nat -> (p + 32 <= 256)%nat ->
  length X0 = 4%nat -> length X1 = 2%nat -> length X2 = 4%nat -> length X3 = 4%nat -> length X4 = 1%nat ->
  length X5 = 8%nat ->
  upd_bytes (upd_bytes (upd_bytes (upd_bytes (upd_bytes (upd_bytes B (p + 4) X1) p X0) (p + 12) X3) (p + 24) X5)
    (p + 8) X2) (p + 16) X4 =
  upd_bytes (upd_bytes (upd_bytes (upd_bytes (upd_bytes B p (X0 ++ X1)) (p + 8) X2) (p + 12) X3) (p + 16) X4)
    (p + 24) X5.
Proof.
  intros B X0 X1 X2 X3 X4 X5 p HB Hp L0 L1 L2 L3 L4 L5.
  replace (p + 4)%nat with (p + length X0)%nat by lia.
  rewrite upd_adj by lia.
  set (B0 := upd_bytes B p (X0 ++ X1)).
  assert (E0 : length B0 = 264%nat) by (unfold B0; rewrite upd_bytes_length; rewrite ?length_app; lia).
  assert (E1 : length (upd_bytes B0 (p + 12) X3) = 264%nat) by (rewrite upd_bytes_length; lia).
  rewrite (upd_comm (upd_bytes B0 (p + 12) X3) (p + 24) X5 (p + 8) X2) by lia.
  assert (E2 : length (upd_bytes (upd_bytes B0 (p + 12) X3) (p + 8) X2) = 264%nat)
    by (rewrite upd_bytes_length; lia).
  rewrite (upd_comm (upd_bytes (upd_bytes B0 (p + 12) X3) (p + 8) X2) (p + 24) X5 (p + 16) X4) by lia.
  rewrite (upd_comm B0 (p + 12) X3 (p + 8) X2) by lia.
  reflexivity.
Qed.

Lemma beq_iff : forall a b, bytes_eqb a b = true <-> map bv_unsigned a = map bv_unsigned b.
Proof.
  intros a b. unfold bytes_eqb. destruct (list_eq_dec Z.eq_dec (map bv_unsigned a) (map bv_unsigned b)).
  - tauto.
  - split; [discriminate | contradiction].
Qed.

Lemma eqb_ulit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Ltac brc E := lazymatch goal with
  | |- evt _ _ (MS _ _ (if negb ?c then _ else _) _ _ _ _) => destruct c eqn:E; cbv beta iota delta [negb]
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:E; cbv beta iota
  end.
