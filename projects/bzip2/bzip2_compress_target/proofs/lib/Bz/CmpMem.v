(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLia.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tab_def {X : Type} (f : Z -> X) (n : Z) : list X := map (fun k => f (Z.of_nat k)) (seq 0 (Z.to_nat n)).
Definition tab_sig : { t : forall X : Type, (Z -> X) -> Z -> list X | forall X, t X = @tab_def X }.
Proof. exists (fun X => @tab_def X). intros; reflexivity. Qed.
Definition tab {X : Type} : (Z -> X) -> Z -> list X := proj1_sig tab_sig X.
Lemma tab_eq : forall {X} (f : Z -> X) n, tab f n = map (fun k => f (Z.of_nat k)) (seq 0 (Z.to_nat n)).
Proof. intros X f n. unfold tab. rewrite (proj2_sig tab_sig X). reflexivity. Qed.

Lemma tab_length_nat : forall {X} (f : Z -> X) n, length (tab f n) = Z.to_nat n.
Proof. intros. rewrite tab_eq, length_map, length_seq. reflexivity. Qed.
Lemma tab_length : forall {X} (f : Z -> X) n, 0 <= n -> Z.of_nat (length (tab f n)) = n.
Proof. intros. rewrite tab_length_nat. lia. Qed.


Lemma nth_error_seq : forall s n k, (k < n)%nat -> nth_error (seq s n) k = Some (s + k)%nat.
Proof.
  intros s n. revert s. induction n as [|n IH]; intros s k Hk; [lia|].
  destruct k as [|k]; cbn; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma tab_nth : forall {X} (f : Z -> X) n i, 0 <= i < n -> nth_error (tab f n) (Z.to_nat i) = Some (f i).
Proof.
  intros X f n i Hi. rewrite tab_eq. rewrite nth_error_map.
  rewrite nth_error_seq by lia. cbn [option_map]. f_equal. f_equal. lia.
Qed.
(* [comment removed for export] *)

Lemma tab_ext : forall {X} (f g : Z -> X) n, (forall i, 0 <= i < n -> f i = g i) -> tab f n = tab g n.
Proof.
  intros X f g n H. rewrite !tab_eq.
  apply map_ext_in. intros k Hk. apply in_seq in Hk. apply H. lia.
Qed.

Lemma upd_map_seq : forall {X} (h : nat -> X) s n k x,
  upd (map h (seq s n)) k x = map (fun j => if Nat.eqb j (s + k) then x else h j) (seq s n).
Proof.
  intros X h s n. revert s. induction n as [|n IH]; intros s k x; [reflexivity|].
  cbn [seq map]. destruct k as [|k]; cbn [upd].
  - rewrite Nat.add_0_r, Nat.eqb_refl. f_equal.
    apply map_ext_in. intros j Hj. apply in_seq in Hj. destruct (Nat.eqb_spec j s); [lia| reflexivity].
  - destruct (Nat.eqb_spec s (s + S k)); [lia|]. f_equal. rewrite IH. apply map_ext_in. intros j _.
    replace (S s + k)%nat with (s + S k)%nat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tab_upd : forall {X} (f g : Z -> X) n i x, 0 <= i < n ->
  g i = x -> (forall j, 0 <= j < n -> j <> i -> g j = f j) ->
  upd (tab f n) (Z.to_nat i) x = tab g n.
Proof.
  intros X f g n i x Hi Hx Hg. rewrite !tab_eq, upd_map_seq. apply map_ext_in. intros k Hk. apply in_seq in Hk.
  destruct (Nat.eqb_spec k (0 + Z.to_nat i)).
  - subst k. rewrite <- Hx. f_equal. lia.
  - symmetry. apply Hg; lia.
Qed.

(* [comment removed for export] *)
Lemma tab_upd_bytes : forall (f g : Z -> byte) n i (bs : list byte), 0 <= i -> i + Z.of_nat (length bs) <= n ->
  (forall k, (k < length bs)%nat -> nth_error bs k = Some (g (i + Z.of_nat k))) ->
  (forall j, 0 <= j < n -> ~ (i <= j < i + Z.of_nat (length bs)) -> g j = f j) ->
  upd_bytes (tab f n) (Z.to_nat i) bs = tab g n.
Proof.
  intros f g n i bs Hi Hn Hin Hout.
  apply nth_error_ext. intros k0.
  destruct (Nat.lt_ge_cases k0 (Z.to_nat n)) as [Hk|Hk].
  - rewrite upd_bytes_nth by (rewrite tab_length_nat; lia).
    remember (Z.of_nat k0) as k eqn:Ek. assert (E : k0 = Z.to_nat k) by lia. assert (Hk0 : 0 <= k < n) by lia. rewrite E in *. clear k0 Ek E.
    rewrite !tab_nth by lia.
    destruct (Nat.leb_spec (Z.to_nat i) (Z.to_nat k)); destruct (Nat.ltb_spec (Z.to_nat k) (Z.to_nat i + length bs)); cbn [andb].
    + rewrite Hin by lia. f_equal. f_equal. lia.
    + f_equal. symmetry. apply Hout; lia.
    + f_equal. symmetry. apply Hout; lia.
    + f_equal. symmetry. apply Hout; lia.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite upd_bytes_length; rewrite ?tab_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite tab_length_nat; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition jw (J : list byte) (k : Z) : word := le_bytes_to_word (firstn 4 (skipn (Z.to_nat (4 * k)) J)).
Definition jb (J : list byte) (k : Z) : byte := nth (Z.to_nat k) J (Z_to_bv 8 0).

Definition zb8 (a : zarr) (n : Z) : list byte := tab (fun i => Z_to_bv 8 (zget a i)) n.
Definition zw32 (a : zarr) (n : Z) : list word := tab (fun i => Z_to_bv 64 (zget a i)) n.
Definition ovb (a : zarr) (J : list byte) (n : Z) : list byte :=
  tab (fun i => if zdef a i then Z_to_bv 8 (zget a i) else jb J i) n.
Definition ovw (a : zarr) (J : list byte) (n : Z) : list word :=
  tab (fun i => if zdef a i then Z_to_bv 64 (zget a i) else jw J i) n.

Lemma zb8_length : forall a n, 0 <= n -> Z.of_nat (length (zb8 a n)) = n. Proof. intros; apply tab_length; assumption. Qed.
Lemma zw32_length : forall a n, 0 <= n -> Z.of_nat (length (zw32 a n)) = n. Proof. intros; apply tab_length; assumption. Qed.
Lemma ovb_length : forall a J n, 0 <= n -> Z.of_nat (length (ovb a J n)) = n. Proof. intros; apply tab_length; assumption. Qed.
Lemma ovw_length : forall a J n, 0 <= n -> Z.of_nat (length (ovw a J n)) = n. Proof. intros; apply tab_length; assumption. Qed.
Lemma zb8_length_nat : forall a n, length (zb8 a n) = Z.to_nat n. Proof. intros; apply tab_length_nat. Qed.
Lemma zw32_length_nat : forall a n, length (zw32 a n) = Z.to_nat n. Proof. intros; apply tab_length_nat. Qed.
Lemma ovb_length_nat : forall a J n, length (ovb a J n) = Z.to_nat n. Proof. intros; apply tab_length_nat. Qed.
Lemma ovw_length_nat : forall a J n, length (ovw a J n) = Z.to_nat n. Proof. intros; apply tab_length_nat. Qed.

Lemma zb8_nth : forall a n i, 0 <= i < n -> nth_error (zb8 a n) (Z.to_nat i) = Some (Z_to_bv 8 (zget a i)).
Proof. intros a n i H. exact (tab_nth (fun j => Z_to_bv 8 (zget a j)) n i H). Qed.
Lemma zw32_nth : forall a n i, 0 <= i < n -> nth_error (zw32 a n) (Z.to_nat i) = Some (Z_to_bv 64 (zget a i)).
Proof. intros a n i H. exact (tab_nth (fun j => Z_to_bv 64 (zget a j)) n i H). Qed.
Lemma ovb_nth : forall a J n i, 0 <= i < n -> zdef a i = true -> nth_error (ovb a J n) (Z.to_nat i) = Some (Z_to_bv 8 (zget a i)).
Proof. intros a J n i Hi Hd. unfold ovb. rewrite (tab_nth (fun j => if zdef a j then Z_to_bv 8 (zget a j) else jb J j)) by assumption. rewrite Hd. reflexivity. Qed.
Lemma ovw_nth : forall a J n i, 0 <= i < n -> zdef a i = true -> nth_error (ovw a J n) (Z.to_nat i) = Some (Z_to_bv 64 (zget a i)).
Proof. intros a J n i Hi Hd. unfold ovw. rewrite (tab_nth (fun j => if zdef a j then Z_to_bv 64 (zget a j) else jw J j)) by assumption. rewrite Hd. reflexivity. Qed.
(* [comment removed for export] *)
Lemma ovb_nth_raw : forall a J n i, 0 <= i < n ->
  nth_error (ovb a J n) (Z.to_nat i) = Some (if zdef a i then Z_to_bv 8 (zget a i) else jb J i).
Proof. intros a J n i H. exact (tab_nth (fun j => if zdef a j then Z_to_bv 8 (zget a j) else jb J j) n i H). Qed.
Lemma ovw_nth_raw : forall a J n i, 0 <= i < n ->
  nth_error (ovw a J n) (Z.to_nat i) = Some (if zdef a i then Z_to_bv 64 (zget a i) else jw J i).
Proof. intros a J n i H. exact (tab_nth (fun j => if zdef a j then Z_to_bv 64 (zget a j) else jw J j) n i H). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zb8_ext : forall a a' n, (forall i, 0 <= i < n -> zget a i = zget a' i) -> zb8 a n = zb8 a' n.
Proof. intros a a' n H. unfold zb8. apply tab_ext. intros i Hi. rewrite H by lia. reflexivity. Qed.
Lemma zw32_ext : forall a a' n, (forall i, 0 <= i < n -> zget a i = zget a' i) -> zw32 a n = zw32 a' n.
Proof. intros a a' n H. unfold zw32. apply tab_ext. intros i Hi. rewrite H by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unsigned_lit8 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof. intros v Hv. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma zxb_lit8 : forall v, 0 <= v < 256 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zxb. rewrite unsigned_lit8 by lia. reflexivity. Qed.
Lemma Z_to_bv8_mod256 : forall v, Z_to_bv 8 (v mod 256) = Z_to_bv 8 v.
Proof. intros v. apply Z_to_bv8_mod. change (2^8) with 256. apply Z.mod_mod. lia. Qed.

Lemma le1_lit : forall w : word, le1 w = [Z_to_bv 8 (bv_unsigned w)].
Proof. intros w. reflexivity. Qed.

Lemma div_mod_pow2 : forall v k j, 0 <= j -> j + 8 <= k -> (v mod 2^k) / 2^j mod 256 = v / 2^j mod 256.
Proof.
  intros v k j Hj Hk. change 256 with (2^8).
  rewrite <- !Z.land_ones by lia. rewrite <- !Z.shiftr_div_pow2 by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  destruct (Z_lt_le_dec i 8).
  - rewrite Z.land_spec. rewrite (Z.ones_spec_low k) by lia. rewrite andb_true_r. reflexivity.
  - rewrite (Z.ones_spec_high 8) by lia. rewrite !andb_false_r. reflexivity.
Qed.
Lemma mod_pow2_mod256 : forall v k, 8 <= k -> (v mod 2^k) mod 256 = v mod 256.
Proof.
  intros v k Hk. pose proof (div_mod_pow2 v k 0 ltac:(lia) ltac:(lia)) as E.
  rewrite !Z.pow_0_r, !Z.div_1_r in E. exact E.
Qed.

Lemma le2_bytes : forall v, le2 (Z_to_bv 64 v) = [Z_to_bv 8 v; Z_to_bv 8 (v / 256)].
Proof.
  intros v. unfold le2. cbn [Z_to_le_bytes]. rewrite unsigned_lit_wrap.
  rewrite Z.shiftr_div_pow2 by lia. change (2^64) with (2^64). f_equal; [|f_equal]; apply Z_to_bv8_mod; change (2^8) with 256.
  - apply mod_pow2_mod256. lia.
  - change 256 with (2^8) at 1 3. apply div_mod_pow2; lia.
Qed.
Lemma le4_bytes : forall v, le4 (Z_to_bv 64 v) = [Z_to_bv 8 v; Z_to_bv 8 (v / 256); Z_to_bv 8 (v / 65536); Z_to_bv 8 (v / 16777216)].
Proof.
  intros v. unfold le4. cbn [Z_to_le_bytes]. rewrite unsigned_lit_wrap.
  rewrite !Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. cbn [Z.add].
  change (2^16) with 65536. change (2^24) with 16777216.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]]; apply Z_to_bv8_mod; change (2^8) with 256.
  - apply mod_pow2_mod256. lia.
  - change 256 with (2^8) at 1 3. apply div_mod_pow2; lia.
  - change 65536 with (2^16). apply div_mod_pow2; lia.
  - change 16777216 with (2^24). apply div_mod_pow2; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Z_to_bv8_plus256 : forall x q, Z_to_bv 8 (x + 256 * q) = Z_to_bv 8 x.
Proof. intros. apply Z_to_bv8_mod. change (2^8) with 256. rewrite Z.mul_comm, Z_mod_plus_full. reflexivity. Qed.
Lemma div256_plus : forall x q, 0 <= x < 256 -> (x + 256 * q) / 256 = q.
Proof. intros x q Hx. rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. lia. Qed.

Lemma le2_recompose : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  [Z_to_bv 8 b0; Z_to_bv 8 b1] = le2 (Z_to_bv 64 (b0 + 256 * b1)).
Proof. intros. rewrite le2_bytes, div256_plus, Z_to_bv8_plus256 by lia. reflexivity. Qed.
Lemma le4_recompose : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 b2; Z_to_bv 8 b3] = le4 (Z_to_bv 64 (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)).
Proof.
  intros. rewrite le4_bytes.
  replace 16777216 with (256 * (256 * 256)) by reflexivity. replace 65536 with (256 * 256) by reflexivity.
  rewrite <- !Z.div_div by lia.
  replace (b0 + 256 * b1 + 256 * 256 * b2 + 256 * (256 * 256) * b3) with (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) by lia.
  rewrite !div256_plus, !Z_to_bv8_plus256 by lia. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma lor_mul256 : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (y * 256) = x + 256 * y.
Proof. intros x y Hx Hy. replace (y * 256) with (Z.shiftl y 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity). apply lor_shiftl8_add; lia. Qed.


Lemma Z_to_bv8_unsigned : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma le4_le_bytes_to_word : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs H. destruct bs as [|b0 [|b1 [|b2 [|b3 [|]]]]]; cbn in H; try lia.
  unfold le_bytes_to_word. cbn [bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R0, R1, R2, R3. change (2 ^ Z.of_N 8)%Z with 256 in R0, R1, R2, R3.
  rewrite Z.shiftl_0_l, Z.lor_0_r. rewrite !Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
  rewrite (lor_mul256 (bv_unsigned b2)) by lia.
  rewrite (lor_mul256 (bv_unsigned b1)) by lia.
  rewrite (lor_mul256 (bv_unsigned b0)) by lia.
  replace (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3)))
    with (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) by lia.
  rewrite <- le4_recompose by lia. rewrite !Z_to_bv8_unsigned. reflexivity.
Qed.

Lemma le4_jw : forall J k, 0 <= k -> (Z.to_nat (4 * k) + 4 <= length J)%nat -> le4 (jw J k) = firstn 4 (skipn (Z.to_nat (4 * k)) J).
Proof. intros J k Hk HL. unfold jw. apply le4_le_bytes_to_word. rewrite firstn_length, skipn_length. lia. Qed.

(* [comment removed for export] *)
Lemma u32s_ext4 : forall ws ws', Forall2 (fun x y => le4 x = le4 y) ws ws' -> u32s ws = u32s ws'.
Proof. intros ws ws' H. induction H; cbn -[le4]; [reflexivity|]. rewrite H, IHForall2. reflexivity. Qed.
Lemma Z_to_le_bytes_mod : forall n z, Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat n)) = Z_to_le_bytes n z.
Proof.
  induction n as [|n IH]; intros z; [reflexivity|].
  cbn [Z_to_le_bytes]. f_equal.
  - apply Z_to_bv8_mod. apply mod_pow2_mod256. lia.
  - rewrite <- (IH (Z.shiftr z 8)), <- (IH (Z.shiftr (z mod _) 8)). f_equal.
    rewrite !Z.shiftr_div_pow2 by lia.
    replace (2 ^ (8 * Z.of_nat (S n))) with (2^8 * 2 ^ (8 * Z.of_nat n)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_nat n) ltac:(lia) ltac:(lia)) as P.
    rewrite Z.rem_mul_r by lia.
    pose proof (Z.mod_pos_bound z (2^8) ltac:(lia)).
    rewrite (Z.mul_comm (2^8)), Z.div_add, (Z.div_small (z mod 2^8)), Z.add_0_l by lia.
    apply Z.mod_mod. lia.
Qed.
Lemma le4_mod32 : forall x y : word, bv_unsigned x mod 2^32 = bv_unsigned y mod 2^32 -> le4 x = le4 y.
Proof.
  intros x y H. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned x)), <- (Z_to_le_bytes_mod 4 (bv_unsigned y)).
  change (8 * Z.of_nat 4) with 32. rewrite H. reflexivity.
Qed.
Lemma le4_lit_mod32 : forall (w : word) v, bv_unsigned w mod 2^32 = v mod 2^32 -> le4 w = le4 (Z_to_bv 64 v).
Proof.
  intros w v H. apply le4_mod32. rewrite unsigned_lit_wrap, H. symmetry.
  change (2^64) with (2^(32+32)). rewrite Z.pow_add_r by lia. apply mod_pow2_mod256 || idtac.
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm (2^32)), Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.

Section Views.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Lemma u8arr_storeN_ok : forall m A bs (i : Z) (n : nat) a,
    u8arr segs m A bs -> 0 <= i -> i + Z.of_nat n <= Z.of_nat (length bs) -> a = wa (A + i) ->
    store_ok segs m a n = true.
  Proof. intros m A bs i n a [_ Hw] Hi Hn ->. eapply wr_at_store_ok; eauto. Qed.
  Lemma u8arr_writeN : forall m A bs (i : Z) (xs : list byte),
    u8arr segs m A bs -> 0 <= i -> (Z.to_nat i + length xs <= length bs)%nat ->
    u8arr segs (write_to_mem m (wa (A + i)) xs) A (upd_bytes bs (Z.to_nat i) xs).
  Proof.
    intros m A bs i xs [Hb Hw] Hi Hl. split.
    - apply bytes_at_write_inside; assumption.
    - rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
  Qed.

  (* [comment removed for export] *)
  Lemma u32arr_ext4 : forall m A ws ws', u32arr segs m A ws -> Forall2 (fun x y => le4 x = le4 y) ws ws' -> u32arr segs m A ws'.
  Proof.
    intros m A ws ws' [Hb Hw] HF. pose proof (Forall2_length HF) as L.
    split; [rewrite <- (u32s_ext4 _ _ HF); exact Hb| rewrite <- L; exact Hw].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma zb8_read1 : forall m A a n i ad, u8arr segs m A (zb8 a n) -> 0 <= i < n -> ad = wa (A + i) ->
    ov_read_bytes segs m ad 1 = Some [Z_to_bv 8 (zget a i)].
  Proof. intros m A a n i ad H Hi ->. eapply u8arr_read; [exact H| apply zb8_nth; lia| lia| reflexivity]. Qed.


  Lemma nth_error_firstn' : forall {X} (l : list X) c k, (k < c)%nat -> nth_error (firstn c l) k = nth_error l k.
  Proof.
    intros X l. induction l as [|x l IH]; intros [|c] [|k] Hk; cbn; try reflexivity; try lia. apply IH. lia.
  Qed.
  Lemma firstn_skipn_nth : forall {X} (l : list X) s c k, (k < c)%nat ->
    nth_error (firstn c (skipn s l)) k = nth_error l (s + k).
  Proof. intros X l s c k Hk. rewrite nth_error_firstn' by exact Hk. rewrite nth_error_skipn. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma tab_window : forall (f : Z -> byte) n i (c : nat) (bs : list byte), 0 <= i -> i + Z.of_nat c <= n ->
    length bs = c -> (forall k, (k < c)%nat -> nth_error bs k = Some (f (i + Z.of_nat k))) ->
    firstn c (skipn (Z.to_nat i) (tab f n)) = bs.
  Proof.
    intros f n i c bs Hi Hn HL Hbs. apply nth_error_ext. intros k.
    destruct (Nat.lt_ge_cases k c) as [Hk|Hk].
    - rewrite firstn_skipn_nth by exact Hk. rewrite Hbs by exact Hk.
      replace (Z.to_nat i + k)%nat with (Z.to_nat (i + Z.of_nat k)) by lia. apply tab_nth. lia.
    - rewrite (proj2 (nth_error_None _ _)) by (rewrite firstn_length, skipn_length, tab_length_nat; lia).
      rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity.
  Qed.

  Lemma zb8_read2 : forall m A a n i ad, u8arr segs m A (zb8 a n) -> 0 <= i -> i + 2 <= n -> zbok a -> ad = wa (A + i) ->
    ov_read_bytes segs m ad 2 = Some (le2 (Z_to_bv 64 (rd16 a i))).
  Proof.
    intros m A a n i ad [Hb _] Hi Hn Hok ->.
    rewrite (bytes_at_read segs m A (zb8 a n) i 2 Hb) by (rewrite ?zb8_length_nat; lia).
    f_equal. unfold rd16. rewrite <- le2_recompose by (apply Hok).
    apply (tab_window _ n i 2); [lia| lia| reflexivity|].
    intros k Hk. destruct k as [|[|k]]; cbn [nth_error]; try lia.
    - f_equal. f_equal. f_equal. lia.
    - reflexivity.
  Qed.

  Lemma zb8_read4 : forall m A a n i ad, u8arr segs m A (zb8 a n) -> 0 <= i -> 4 * i + 4 <= n -> zbok a -> ad = wa (A + 4 * i) ->
    ov_read_bytes segs m ad 4 = Some (le4 (Z_to_bv 64 (rd32 a i))).
  Proof.
    intros m A a n i ad [Hb _] Hi Hn Hok ->.
    rewrite (bytes_at_read segs m A (zb8 a n) (4 * i) 4 Hb) by (rewrite ?zb8_length_nat; lia).
    f_equal. unfold rd32. rewrite <- le4_recompose by (apply Hok).
    apply (tab_window _ n (4 * i) 4); [lia| lia| reflexivity|].
    intros k Hk. destruct k as [|[|[|[|k]]]]; cbn [nth_error]; try lia.
    - f_equal. f_equal. f_equal. lia.
    - reflexivity. - reflexivity. - reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma zb8_write1 : forall m A a n i (w : word), u8arr segs m A (zb8 a n) -> 0 <= i < n ->
    u8arr segs (write_to_mem m (wa (A + i)) (le1 w)) A (zb8 (wr8 a i (bv_unsigned w)) n).
  Proof.
    intros m A a n i w H Hi. rewrite le1_lit.
    pose proof (u8arr_write segs m A (zb8 a n) i (Z_to_bv 8 (bv_unsigned w)) H ltac:(rewrite zb8_length_nat; lia)) as W.
    unfold zb8 in W |- *. erewrite tab_upd in W; [exact W| lia| |].
    - cbn beta. unfold wr8. rewrite zget_zset_same. apply Z_to_bv8_mod256.
    - intros j Hj Hne. cbn beta. unfold wr8. rewrite zget_zset_other by exact Hne. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma zb8_write1_lit : forall m A a n i z, u8arr segs m A (zb8 a n) -> 0 <= i < n ->
    u8arr segs (write_to_mem m (wa (A + i)) [Z_to_bv 8 z]) A (zb8 (wr8 a i z) n).
  Proof.
    intros m A a n i z H Hi.
    pose proof (u8arr_write segs m A (zb8 a n) i (Z_to_bv 8 z) H ltac:(rewrite zb8_length_nat; lia)) as W.
    unfold zb8 in W |- *. erewrite tab_upd in W; [exact W| lia| |].
    - cbn beta. unfold wr8. rewrite zget_zset_same. apply Z_to_bv8_mod256.
    - intros j Hj Hne. cbn beta. unfold wr8. rewrite zget_zset_other by exact Hne. reflexivity.
  Qed.


  Lemma le2_unsigned : forall w : word, le2 w = [Z_to_bv 8 (bv_unsigned w); Z_to_bv 8 (bv_unsigned w / 256)].
  Proof. intros w. rewrite <- le2_bytes. f_equal. symmetry. apply bv_eq. rewrite unsigned_lit by (pose proof (bv_unsigned_in_range 64 w); unfold bv_modulus in *; cbn in *; lia). reflexivity. Qed.
  Lemma le4_unsigned : forall w : word,
    le4 w = [Z_to_bv 8 (bv_unsigned w); Z_to_bv 8 (bv_unsigned w / 256); Z_to_bv 8 (bv_unsigned w / 65536); Z_to_bv 8 (bv_unsigned w / 16777216)].
  Proof. intros w. rewrite <- le4_bytes. f_equal. symmetry. apply bv_eq. rewrite unsigned_lit by (pose proof (bv_unsigned_in_range 64 w); unfold bv_modulus in *; cbn in *; lia). reflexivity. Qed.

  Lemma zb8_write2 : forall m A a n i (w : word), u8arr segs m A (zb8 a n) -> 0 <= i -> i + 2 <= n ->
    u8arr segs (write_to_mem m (wa (A + i)) (le2 w)) A (zb8 (wr16 a i (bv_unsigned w)) n).
  Proof.
    intros m A a n i w H Hi Hn.
    pose proof (u8arr_writeN m A (zb8 a n) i (le2 w) H Hi ltac:(rewrite length_le2, zb8_length_nat; lia)) as W.
    unfold zb8 in W |- *. erewrite tab_upd_bytes in W; [exact W| lia| rewrite length_le2; lia| |].
    - intros k Hk. rewrite length_le2 in Hk. rewrite le2_unsigned. unfold wr16.
      destruct k as [|[|k]]; [| | lia]; cbn [nth_error Z.of_nat Pos.of_succ_nat].
      + rewrite Z.add_0_r, zget_zset_other, zget_zset_same by lia. rewrite Z_to_bv8_mod256. reflexivity.
      + rewrite zget_zset_same. rewrite Z_to_bv8_mod256. reflexivity.
    - intros j Hj Hnot. rewrite length_le2 in Hnot. cbn beta. unfold wr16. rewrite !zget_zset_other by lia. reflexivity.
  Qed.

  Lemma zb8_write4 : forall m A a n i (w : word), u8arr segs m A (zb8 a n) -> 0 <= i -> 4 * i + 4 <= n ->
    u8arr segs (write_to_mem m (wa (A + 4 * i)) (le4 w)) A (zb8 (wr32 a i (bv_unsigned w)) n).
  Proof.
    intros m A a n i w H Hi Hn.
    pose proof (u8arr_writeN m A (zb8 a n) (4 * i) (le4 w) H ltac:(lia) ltac:(rewrite length_le4, zb8_length_nat; lia)) as W.
    unfold zb8 in W |- *. erewrite tab_upd_bytes in W; [exact W| lia| rewrite length_le4; lia| |].
    - intros k Hk. rewrite length_le4 in Hk. rewrite le4_unsigned. unfold wr32.
      destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ].
      + rewrite Z.add_0_r, !zget_zset_other, zget_zset_same by lia. rewrite Z_to_bv8_mod256. reflexivity.
      + rewrite 2 zget_zset_other, zget_zset_same by lia. rewrite Z_to_bv8_mod256. reflexivity.
      + rewrite zget_zset_other, zget_zset_same by lia. rewrite Z_to_bv8_mod256. reflexivity.
      + rewrite zget_zset_same. rewrite Z_to_bv8_mod256. reflexivity.
    - intros j Hj Hnot. rewrite length_le4 in Hnot. cbn beta. unfold wr32. rewrite !zget_zset_other by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma zb8_init : forall m A n (bs : list byte), rw_cells segs m A [CB (Z.to_nat n) bs] -> 0 <= n ->
    (forall k b, nth_error bs k = Some b -> b = Z_to_bv 8 0) -> u8arr segs m A (zb8 znew n).
  Proof.
    intros m A n bs H Hn Hz. pose proof (u8arr_of_rw_cells segs m A _ bs H) as U.
    replace (zb8 znew n) with bs; [exact U|].
    destruct H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [HL _].
    apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k (Z.to_nat n)) as [Hk|Hk].
    - replace k with (Z.to_nat (Z.of_nat k)) by lia. unfold zb8. rewrite tab_nth by lia. rewrite zget_znew.
      destruct (nth_error bs (Z.to_nat (Z.of_nat k))) as [b|] eqn:E; [rewrite (Hz _ _ E); reflexivity|].
      apply nth_error_None in E. lia.
    - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by (rewrite zb8_length_nat; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma zw32_read : forall m A a n i ad, u32arr segs m A (zw32 a n) -> 0 <= i < n -> ad = wa (A + 4 * i) ->
    ov_read_bytes segs m ad 4 = Some (le4 (Z_to_bv 64 (zget a i))).
  Proof. intros m A a n i ad H Hi ->. eapply u32arr_read; [exact H| apply zw32_nth; lia| lia| reflexivity]. Qed.

  Lemma zw32_write : forall m A a n i (w : word) v, u32arr segs m A (zw32 a n) -> 0 <= i < n ->
    bv_unsigned w mod 2^32 = v mod 2^32 ->
    u32arr segs (write_to_mem m (wa (A + 4 * i)) (le4 w)) A (zw32 (zset a i v) n).
  Proof.
    intros m A a n i w v H Hi Hv.
    pose proof (u32arr_write segs m A (zw32 a n) i w H ltac:(rewrite zw32_length_nat; lia)) as W.
    eapply u32arr_ext4; [exact W|].
    unfold zw32. erewrite (tab_upd _ (fun j => if j =? i then w else Z_to_bv 64 (zget a j))); [| lia| rewrite Z.eqb_refl; reflexivity|].
    2:{ intros j Hj Hne. cbn beta. destruct (Z.eqb_spec j i); [lia| reflexivity]. }
    rewrite !tab_eq. remember (seq 0 (Z.to_nat n)) as l. clear -Hv.
    induction l as [|k l IH]; cbn [map]; constructor; [|exact IH].
    rewrite zget_zset. destruct (Z.of_nat k =? i); [|reflexivity]. apply le4_lit_mod32. exact Hv.
  Qed.

  Lemma u32s_zero_seq : forall c s,
    u32s (map (fun k => Z_to_bv 64 (zget znew (Z.of_nat k))) (seq s c)) = repeat (Z_to_bv 8 0) (4 * c).
  Proof.
    induction c as [|c IH]; intros s; [reflexivity|].
    cbn [seq map u32s]. rewrite zget_znew, IH.
    replace (4 * S c)%nat with (S (S (S (S (4 * c)))))%nat by lia. reflexivity.
  Qed.

  Lemma zw32_init : forall m A n (bs : list byte), rw_cells segs m A [CB (Z.to_nat (4 * n)) bs] -> 0 <= n ->
    (forall k b, nth_error bs k = Some b -> b = Z_to_bv 8 0) -> u32arr segs m A (zw32 znew n).
  Proof.
    intros m A n bs H Hn Hz. destruct H as [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [HL _].
    cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
    assert (E : u32s (zw32 znew n) = bs).
    { unfold zw32. rewrite tab_eq, u32s_zero_seq.
      apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k (Z.to_nat (4 * n))) as [Hk|Hk].
      - destruct (nth_error bs k) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia]. rewrite (Hz _ _ Eb).
        apply nth_error_repeat. lia.
      - rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia).
        rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity. }
    split; [rewrite E; exact Hb| rewrite zw32_length_nat; replace (4 * Z.of_nat (Z.to_nat n)) with (Z.of_nat (Z.to_nat (4 * n))) by lia; exact Hw].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ovb_read1 : forall m A a J n i ad, u8arr segs m A (ovb a J n) -> 0 <= i < n -> zdef a i = true -> ad = wa (A + i) ->
    ov_read_bytes segs m ad 1 = Some [Z_to_bv 8 (zget a i)].
  Proof. intros m A a J n i ad H Hi Hd ->. eapply u8arr_read; [exact H| apply ovb_nth; assumption| lia| reflexivity]. Qed.

  Lemma ovb_write1 : forall m A a J n i (w : word), u8arr segs m A (ovb a J n) -> 0 <= i < n ->
    u8arr segs (write_to_mem m (wa (A + i)) (le1 w)) A (ovb (wr8 a i (bv_unsigned w)) J n).
  Proof.
    intros m A a J n i w H Hi. rewrite le1_lit.
    pose proof (u8arr_write segs m A (ovb a J n) i (Z_to_bv 8 (bv_unsigned w)) H ltac:(rewrite ovb_length_nat; lia)) as W.
    unfold ovb in W |- *. erewrite tab_upd in W; [exact W| lia| |].
    - cbn beta. unfold wr8. rewrite zdef_zset_same, zget_zset_same. apply Z_to_bv8_mod256.
    - intros j Hj Hne. cbn beta. unfold wr8. rewrite zdef_zset_other, zget_zset_other by exact Hne. reflexivity.
  Qed.
  Lemma ovb_write1_lit : forall m A a J n i z, u8arr segs m A (ovb a J n) -> 0 <= i < n ->
    u8arr segs (write_to_mem m (wa (A + i)) [Z_to_bv 8 z]) A (ovb (wr8 a i z) J n).
  Proof.
    intros m A a J n i z H Hi.
    pose proof (u8arr_write segs m A (ovb a J n) i (Z_to_bv 8 z) H ltac:(rewrite ovb_length_nat; lia)) as W.
    unfold ovb in W |- *. erewrite tab_upd in W; [exact W| lia| |].
    - cbn beta. unfold wr8. rewrite zdef_zset_same, zget_zset_same. apply Z_to_bv8_mod256.
    - intros j Hj Hne. cbn beta. unfold wr8. rewrite zdef_zset_other, zget_zset_other by exact Hne. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma ovb_write1_zset : forall m A a J n i z, u8arr segs m A (ovb a J n) -> 0 <= i < n -> 0 <= z < 256 ->
    u8arr segs (write_to_mem m (wa (A + i)) [Z_to_bv 8 z]) A (ovb (zset a i z) J n).
  Proof.
    intros m A a J n i z H Hi Hz. pose proof (ovb_write1_lit m A a J n i z H Hi) as W.
    unfold wr8 in W. rewrite Z.mod_small in W by exact Hz. exact W.
  Qed.

  Lemma ovb_init : forall m A n (J : list byte), rw_cells segs m A [CB (Z.to_nat n) J] -> 0 <= n ->
    u8arr segs m A (ovb znew J n).
  Proof.
    intros m A n J H Hn. pose proof (u8arr_of_rw_cells segs m A _ J H) as U.
    replace (ovb znew J n) with J; [exact U|].
    destruct H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [HL _].
    apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k (Z.to_nat n)) as [Hk|Hk].
    - replace k with (Z.to_nat (Z.of_nat k)) by lia. unfold ovb. rewrite tab_nth by lia. rewrite zdef_znew.
      unfold jb. rewrite Nat2Z.id. symmetry. symmetry. apply nth_error_nth'. lia.
    - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by (rewrite ovb_length_nat; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ovw_read : forall m A a J n i ad, u32arr segs m A (ovw a J n) -> 0 <= i < n -> zdef a i = true -> ad = wa (A + 4 * i) ->
    ov_read_bytes segs m ad 4 = Some (le4 (Z_to_bv 64 (zget a i))).
  Proof. intros m A a J n i ad H Hi Hd ->. eapply u32arr_read; [exact H| apply ovw_nth; assumption| lia| reflexivity]. Qed.

  Lemma ovw_write : forall m A a J n i (w : word) v, u32arr segs m A (ovw a J n) -> 0 <= i < n ->
    bv_unsigned w mod 2^32 = v mod 2^32 ->
    u32arr segs (write_to_mem m (wa (A + 4 * i)) (le4 w)) A (ovw (zset a i v) J n).
  Proof.
    intros m A a J n i w v H Hi Hv.
    pose proof (u32arr_write segs m A (ovw a J n) i w H ltac:(rewrite ovw_length_nat; lia)) as W.
    eapply u32arr_ext4; [exact W|].
    unfold ovw. erewrite (tab_upd _ (fun j => if j =? i then w else if zdef a j then Z_to_bv 64 (zget a j) else jw J j));
      [| lia| rewrite Z.eqb_refl; reflexivity|].
    2:{ intros j Hj Hne. cbn beta. destruct (Z.eqb_spec j i); [lia| reflexivity]. }
    rewrite !tab_eq. remember (seq 0 (Z.to_nat n)) as l. clear -Hv.
    induction l as [|k l IH]; cbn [map]; constructor; [|exact IH].
    rewrite zdef_zset, zget_zset. destruct (Z.of_nat k =? i); cbn [orb]; [|reflexivity]. apply le4_lit_mod32. exact Hv.
  Qed.

  Lemma firstn_add_skipn : forall {X} (l : list X) a b, firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
  Proof.
    intros X l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
    destruct l as [|x l]; cbn; [now destruct b|]. rewrite IH. reflexivity.
  Qed.
  Lemma u32s_jw_seq : forall c s J, (4 * (s + c) <= length J)%nat ->
    u32s (map (fun k => jw J (Z.of_nat k)) (seq s c)) = firstn (4 * c) (skipn (4 * s) J).
  Proof.
    induction c as [|c IH]; intros s J HL.
    - cbn. symmetry. apply firstn_O.
    - cbn [seq map u32s]. rewrite IH by lia. rewrite le4_jw by lia.
      replace (Z.to_nat (4 * Z.of_nat s)) with (4 * s)%nat by lia.
      replace (4 * S c)%nat with (4 + 4 * c)%nat by lia. rewrite firstn_add_skipn, skipn_skipn.
      replace (4 + 4 * s)%nat with (4 * S s)%nat by lia. reflexivity.
  Qed.

  Lemma ovw_init : forall m A n (J : list byte), rw_cells segs m A [CB (Z.to_nat (4 * n)) J] -> 0 <= n ->
    u32arr segs m A (ovw znew J n).
  Proof.
    intros m A n J H Hn. destruct H as [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [HL _].
    cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
    assert (E : u32s (ovw znew J n) = J).
    { unfold ovw. rewrite tab_eq.
      rewrite (map_ext _ (fun k => jw J (Z.of_nat k))) by (intros k; rewrite zdef_znew; reflexivity).
      rewrite u32s_jw_seq by lia. cbn [skipn].
      replace (4 * Z.to_nat n)%nat with (length J) by lia. apply firstn_all. }
    split; [rewrite E; exact Hb| rewrite ovw_length_nat; replace (4 * Z.of_nat (Z.to_nat n)) with (Z.of_nat (Z.to_nat (4 * n))) by lia; exact Hw].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ovw_defined_zw32 : forall a J n, (forall i, 0 <= i < n -> zdef a i = true) -> ovw a J n = zw32 a n.
  Proof. intros a J n H. unfold ovw, zw32. apply tab_ext. intros i Hi. rewrite H by exact Hi. reflexivity. Qed.
  Lemma ovb_defined_zb8 : forall a J n, (forall i, 0 <= i < n -> zdef a i = true) -> ovb a J n = zb8 a n.
  Proof. intros a J n H. unfold ovb, zb8. apply tab_ext. intros i Hi. rewrite H by exact Hi. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma ovw_ext : forall a a' J n, (forall i, 0 <= i < n -> zdef a i = zdef a' i /\ zget a i = zget a' i) -> ovw a J n = ovw a' J n.
  Proof. intros a a' J n H. unfold ovw. apply tab_ext. intros i Hi. destruct (H i Hi) as [-> ->]. reflexivity. Qed.
  Lemma ovb_ext : forall a a' J n, (forall i, 0 <= i < n -> zdef a i = zdef a' i /\ zget a i = zget a' i) -> ovb a J n = ovb a' J n.
  Proof. intros a a' J n H. unfold ovb. apply tab_ext. intros i Hi. destruct (H i Hi) as [-> ->]. reflexivity. Qed.
End Views.
End ACeilS1.


(* [comment removed for export] *)
#[global] Opaque zb8 zw32 ovb ovw jw jb.
Arguments zb8 : simpl never. Arguments zw32 : simpl never. Arguments ovb : simpl never. Arguments ovw : simpl never.
