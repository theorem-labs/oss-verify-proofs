(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgMem.v at 22fdb2585dec (the proofs of its byte-list lemmas rm_byte_range, rm_unsigned_byte, rm_le_byte_1, rm_le_byte_bv, rm_nth_le_bytes, rm_nth_map, rm_nth_repeat, rm_aview_mbyte and of rm_bytes_kept); restated over garr8 and val_mem with the pwm_ prefix, with no image and no frame; the lemmas on Pod/Layout.v's ent_mem and Pod/Model.v's enc_pod are new. *)
(* The memory helper lemmas of the walk of pod_write_ent on reac-pw/fuzz_rate's image B. Proves no function (kind:
   model lemma). Every lemma is over the shared kit's predicates (garr8, val_mem, mbyte, aview, range_addressable,
   shadow_hull_vis), generic in the segments segs: no image, no address and no unit-dependent number is named here.

   1. Byte arithmetic: le_byte (the one val_mem reads, YO0f.le_byte), the bytes of Z_to_le_bytes, Cursor.le32 and
      Cursor.zeros as lists of Z.
   2. Bytes at an address: one byte (val_mem ... 1 <-> mbyte), a field of a byte list read as an n-byte
      little-endian value, a byte list from per-byte facts, a list split in two, the bytes of an n-byte value.
   3. Facts kept across a write that misses them: a byte list, an n-byte value, the shadow of a range
      (range_addressable) and the readability of a shadow hull.
   4. The pod entry's fields (Layout.ent_mem e as a list of Z): its length, its type and size words, its body.
   5. The bytes pod_write_ent writes: the length of Model.enc_pod e, the pad, and the key lemma pwm_enc_of_parts:
      the size word, the type word, the body and the zero pad, at a, a + 4, a + 8 and a + 8 + size, are the bytes of
      Model.enc_pod e at a. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YP09 YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout Cursor.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================================== 1. byte arithmetic ======================================== *)
Lemma pwm_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma pwm_unsigned_byte : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma pwm_le_byte_range : forall v n k, 0 <= YO0f.le_byte v n k < 256.
Proof. intros v n k. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma pwm_le_byte_1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma pwm_le_byte_bv : forall v n k, (k < n)%nat ->
Z_to_bv 8 (YO0f.le_byte v n k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
intros v n k Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). unfold YO0f.le_byte. change 256 with (2 ^ 8). rewrite Z.mod_mod by lia.
apply Z.bits_inj'. intros i Hi. destruct (Z_lt_le_dec i 8) as [Hl|Hg].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma pwm_nth_le_shiftr : forall n v k, (k < n)%nat ->
nth k (Z_to_le_bytes n v) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros v k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- rewrite Nat2Z.inj_0, Z.mul_0_r, Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma pwm_le_bytes_nth : forall n v k, (k < n)%nat ->
nth k (Z_to_le_bytes n v) (Z_to_bv 8 0) = Z_to_bv 8 (YO0f.le_byte v n k).
Proof. intros n v k Hk. rewrite pwm_nth_le_shiftr, pwm_le_byte_bv by exact Hk. reflexivity. Qed.

Lemma pwm_nth_map : forall (l : list byte) j,
nth j (map (fun x : byte => bv_unsigned x) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. induction l as [|b l IH]; intros [|j]; cbn [map nth]; try reflexivity. apply IH. Qed.

Lemma pwm_nth_repeat : forall (x d : byte) n i, (i < n)%nat -> nth i (repeat x n) d = x.
Proof. intros x d n. induction n as [|n IH]; intros [|i] Hi; cbn [repeat nth]; [lia | lia | reflexivity | apply IH; lia]. Qed.

Lemma pwm_length_le32 : forall v, length (Cursor.le32 v) = 4%nat.
Proof. intros v. unfold Cursor.le32. apply length_Z_to_le_bytes. Qed.

Lemma pwm_length_zeros : forall n, length (Cursor.zeros n) = n.
Proof. intros n. unfold Cursor.zeros. apply repeat_length. Qed.

(* byte k of the le32 word of v, as the Z the byte list holds *)
Lemma pwm_le32_nth : forall v k, (k < 4)%nat ->
nth k (map (fun x : byte => bv_unsigned x) (Cursor.le32 v)) 0 = YO0f.le_byte v 4 k.
Proof.
intros v k Hk. rewrite pwm_nth_map. unfold Cursor.le32. rewrite pwm_le_bytes_nth by exact Hk.
rewrite pwm_unsigned_byte. apply Z.mod_small. apply pwm_le_byte_range.
Qed.

Lemma pwm_pad8_range : forall n, 0 <= Model.pad8 n < 8.
Proof. intros n. unfold Model.pad8. apply Z.mod_pos_bound. lia. Qed.

Lemma pwm_pad8_mod : forall n, (n + Model.pad8 n) mod 8 = 0.
Proof.
intros n. unfold Model.pad8. rewrite Z.add_mod_idemp_r by lia.
replace (n + (8 - n mod 8)) with ((n / 8 + 1) * 8) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
apply Z.mod_mul. lia.
Qed.

Section m.
Variable segs : list Segment.

(* ====================================== 2. bytes at an address ====================================== *)
Lemma pwm_byte_val : forall m a v, 0 <= v < 256 ->
val_mem segs m a 1 v <-> mbyte segs m a = Some (Z_to_bv 8 v).
Proof.
intros m a v Hv. unfold val_mem. split.
- intros V. specialize (V 0%nat ltac:(lia)). cbn [Z.of_nat] in V. rewrite Z.add_0_r, pwm_le_byte_1 in V by exact Hv.
  exact V.
- intros E k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, pwm_le_byte_1 by exact Hv.
  exact E.
Qed.

Lemma pwm_garr8_field : forall m a (l : list Z) (o n : nat) (v : Z),
garr8 segs m a l -> (o + n <= length l)%nat ->
(forall k, (k < n)%nat -> nth (o + k) l 0 = YO0f.le_byte v n k) ->
val_mem segs m (a + Z.of_nat o) n v.
Proof.
intros m a l o n v G Hl E k Hk.
replace (a + Z.of_nat o + Z.of_nat k) with (a + Z.of_nat (o + k)) by lia.
rewrite (garr8_mbyte segs m a l (o + k) G ltac:(lia)), (E k Hk). reflexivity.
Qed.

Lemma pwm_garr8_of_bytes : forall m a (l : list Z),
(forall j, (j < length l)%nat -> mbyte segs m (a + Z.of_nat j) = Some (Z_to_bv 8 (nth j l 0))) ->
(forall j, (j < length l)%nat -> 0 <= nth j l 0 < 256) ->
garr8 segs m a l.
Proof.
intros m a l Hb Hr j Hj. split; [|exact (Hr j Hj)].
apply pwm_byte_val; [exact (Hr j Hj) | exact (Hb j Hj)].
Qed.

Lemma pwm_garr8_app : forall m a l1 l2,
garr8 segs m a (l1 ++ l2) <-> garr8 segs m a l1 /\ garr8 segs m (a + Z.of_nat (length l1)) l2.
Proof. intros m a l1 l2. exact (garr8_app segs m a l1 l2). Qed.

(* the n bytes of the value v at a, as the byte list of Z_to_le_bytes n v, and back *)
Lemma pwm_garr8_of_val : forall m a n v,
val_mem segs m a n v -> garr8 segs m a (map (fun x : byte => bv_unsigned x) (Z_to_le_bytes n v)).
Proof.
intros m a n v V. apply pwm_garr8_of_bytes.
- intros j Hj. rewrite length_map, length_Z_to_le_bytes in Hj.
  rewrite pwm_nth_map, Z_to_bv_bv_unsigned, pwm_le_bytes_nth by exact Hj. exact (V j Hj).
- intros j _. rewrite pwm_nth_map. apply pwm_byte_range.
Qed.

Lemma pwm_val_of_garr8 : forall m a n v,
garr8 segs m a (map (fun x : byte => bv_unsigned x) (Z_to_le_bytes n v)) -> val_mem segs m a n v.
Proof.
intros m a n v G. replace a with (a + Z.of_nat 0) by lia.
apply (pwm_garr8_field m a _ 0 n v G); [rewrite length_map, length_Z_to_le_bytes; lia|].
intros k Hk. cbn [Nat.add]. rewrite pwm_nth_map, pwm_le_bytes_nth by exact Hk.
rewrite pwm_unsigned_byte. apply Z.mod_small. apply pwm_le_byte_range.
Qed.

(* n zero bytes at b *)
Lemma pwm_garr8_zeros : forall m b n,
(forall i, 0 <= i < Z.of_nat n -> mbyte segs m (b + i) = Some (Z_to_bv 8 0)) ->
garr8 segs m b (map (fun x : byte => bv_unsigned x) (Cursor.zeros n)).
Proof.
intros m b n Hz. apply pwm_garr8_of_bytes.
- intros j Hj. rewrite length_map, pwm_length_zeros in Hj.
  rewrite pwm_nth_map, Z_to_bv_bv_unsigned. unfold Cursor.zeros. rewrite pwm_nth_repeat by exact Hj.
  apply Hz. lia.
- intros j _. rewrite pwm_nth_map. apply pwm_byte_range.
Qed.

(* ================================ 3. facts kept across a write ================================ *)
Lemma pwm_aview_mbyte : forall H mem x (b : byte),
aview segs H mem x = Some (bv_unsigned b) -> mbyte segs (mrestrict H mem) x = Some b.
Proof.
intros H mem x b A. unfold aview in A. destruct (mbyte segs (mrestrict H mem) x) as [b'|] eqn:E; [|discriminate A].
cbn [option_map] in A. injection A as A. f_equal. apply bv_eq. exact A.
Qed.

Lemma pwm_mbyte_kept : forall (H H' : word -> bool) m m' x (b : byte),
aview segs H' m' x = aview segs H m x -> mbyte segs (mrestrict H m) x = Some b ->
mbyte segs (mrestrict H' m') x = Some b.
Proof.
intros H H' m m' x b K V. apply pwm_aview_mbyte. rewrite K. unfold aview. rewrite V. reflexivity.
Qed.

Lemma pwm_garr8_kept : forall (H H' : word -> bool) m m' a l,
garr8 segs (mrestrict H m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview segs H' m' x = aview segs H m x) ->
garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l G K. apply pwm_garr8_of_bytes.
- intros j Hj. apply (pwm_mbyte_kept H H' m m'); [apply K; lia | exact (garr8_mbyte segs _ a l j G Hj)].
- intros j Hj. exact (proj2 (G j Hj)).
Qed.

Lemma pwm_val_mem_kept : forall (H H' : word -> bool) m m' a n v,
val_mem segs (mrestrict H m) a n v ->
(forall x, a <= x < a + Z.of_nat n -> aview segs H' m' x = aview segs H m x) ->
val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v V K k Hk. apply (pwm_mbyte_kept H H' m m'); [apply K; lia | exact (V k Hk)].
Qed.

Lemma pwm_ra_kept : forall (H H' : word -> bool) m m' a n Ks,
range_addressable (aview segs H m) Ks a n ->
(forall x, a <= x < a + n -> aview segs H' m' (shadow_of_addr Ks x) = aview segs H m (shadow_of_addr Ks x)) ->
range_addressable (aview segs H' m') Ks a n.
Proof. intros H H' m m' a n Ks R K x Hx. rewrite (K x Hx). exact (R x Hx). Qed.

Lemma pwm_hull_kept : forall (H H' : word -> bool) m m' x n,
shadow_hull_vis (aview segs H m) x n ->
(forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
 aview segs H m s <> None -> aview segs H' m' s <> None) ->
shadow_hull_vis (aview segs H' m') x n.
Proof. intros H H' m m' x n Hh K s Hs. exact (K s Hs (Hh s Hs)). Qed.

(* the same when the hull's shadow bytes are unchanged *)
Lemma pwm_hull_kept_eq : forall (H H' : word -> bool) m m' x n,
shadow_hull_vis (aview segs H m) x n ->
(forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
 aview segs H' m' s = aview segs H m s) ->
shadow_hull_vis (aview segs H' m') x n.
Proof. intros H H' m m' x n Hh K s Hs. rewrite (K s Hs). exact (Hh s Hs). Qed.

(* ================================ 4. the pod entry's fields ================================ *)
Lemma pwm_ent_len_eq : forall e,
length (map (fun x : byte => bv_unsigned x) (Layout.ent_mem e))
= (8 + length (Model.e_body e) + (96 - length (Model.e_body e)))%nat.
Proof.
intros e. rewrite length_map. unfold Layout.ent_mem.
rewrite !length_app, !pwm_length_le32, pwm_length_zeros. lia.
Qed.

Lemma pwm_ent_len : forall e, (length (Model.e_body e) <= 96)%nat ->
length (map (fun x : byte => bv_unsigned x) (Layout.ent_mem e)) = 104%nat.
Proof. intros e He. rewrite pwm_ent_len_eq. lia. Qed.

Lemma pwm_ent_nth_type : forall e k, (k < 4)%nat ->
nth k (map (fun x : byte => bv_unsigned x) (Layout.ent_mem e)) 0 = YO0f.le_byte (Model.e_type e) 4 k.
Proof.
intros e k Hk. unfold Layout.ent_mem. rewrite map_app.
rewrite app_nth1 by (rewrite length_map, pwm_length_le32; exact Hk). apply pwm_le32_nth. exact Hk.
Qed.

Lemma pwm_ent_nth_size : forall e k, (k < 4)%nat ->
nth (4 + k) (map (fun x : byte => bv_unsigned x) (Layout.ent_mem e)) 0 = YO0f.le_byte (Model.e_size e) 4 k.
Proof.
intros e k Hk. unfold Layout.ent_mem. rewrite map_app.
rewrite app_nth2 by (rewrite length_map, pwm_length_le32; lia).
rewrite length_map, pwm_length_le32. replace (4 + k - 4)%nat with k by lia.
rewrite map_app. rewrite app_nth1 by (rewrite length_map, pwm_length_le32; exact Hk).
apply pwm_le32_nth. exact Hk.
Qed.

Lemma pwm_ent_type : forall m a e,
garr8 segs m a (map (fun x : byte => bv_unsigned x) (Layout.ent_mem e)) -> 0 <= Model.e_type e < 2 ^ 32 ->
val_mem segs m a 4 (Model.e_type e).
Proof.
intros m a e G _. replace a with (a + Z.of_nat 0) by lia.
apply (pwm_garr8_field m a _ 0 4 _ G); [rewrite pwm_ent_len_eq; lia|].
intros k Hk. cbn [Nat.add]. apply pwm_ent_nth_type. exact Hk.
Qed.

Lemma pwm_ent_size : forall m a e,
garr8 segs m a (map (fun x : byte => bv_unsigned x) (Layout.ent_mem e)) -> 0 <= Model.e_size e < 2 ^ 32 ->
val_mem segs m (a + 4) 4 (Model.e_size e).
Proof.
intros m a e G _. replace (a + 4) with (a + Z.of_nat 4) by lia.
apply (pwm_garr8_field m a _ 4 4 _ G); [rewrite pwm_ent_len_eq; lia|].
intros k Hk. apply pwm_ent_nth_size. exact Hk.
Qed.

Lemma pwm_ent_body : forall m a e,
garr8 segs m a (map (fun x : byte => bv_unsigned x) (Layout.ent_mem e)) ->
Z.of_nat (length (Model.e_body e)) = Model.e_size e -> Model.e_size e <= 96 ->
garr8 segs m (a + 8) (map (fun x : byte => bv_unsigned x) (Model.e_body e)).
Proof.
intros m a e G _ _. unfold Layout.ent_mem in G. rewrite !map_app in G.
apply pwm_garr8_app in G as [_ G]. apply pwm_garr8_app in G as [_ G]. apply pwm_garr8_app in G as [G _].
rewrite !length_map, !pwm_length_le32 in G.
replace (a + Z.of_nat 4 + Z.of_nat 4) with (a + 8) in G by lia. exact G.
Qed.

(* ============================== 5. the bytes pod_write_ent writes ============================== *)
Lemma pwm_enc_split : forall e,
Model.enc_pod e = Cursor.le32 (Model.e_size e) ++ Cursor.le32 (Model.e_type e)
++ Model.e_body e ++ Cursor.zeros (Z.to_nat (Model.pad8 (Model.e_size e))).
Proof. intros e. reflexivity. Qed.

Lemma pwm_enc_len : forall e,
Z.of_nat (length (Model.e_body e)) = Model.e_size e -> 0 <= Model.e_size e <= 96 ->
Z.of_nat (length (Model.enc_pod e)) = 8 + Model.e_size e + Model.pad8 (Model.e_size e).
Proof.
intros e Hl _. pose proof (pwm_pad8_range (Model.e_size e)) as P.
rewrite pwm_enc_split, !length_app, !pwm_length_le32, pwm_length_zeros.
rewrite !Nat2Z.inj_add, Z2Nat.id by lia. lia.
Qed.

(* THE key lemma: the size word at a, the type word at a + 4, the body at a + 8 and the zero pad at a + 8 + size
   are the bytes of Model.enc_pod e at a. *)
Lemma pwm_enc_of_parts : forall m a e,
Z.of_nat (length (Model.e_body e)) = Model.e_size e ->
0 <= Model.e_size e <= 96 -> 0 <= Model.e_type e < 2 ^ 32 ->
val_mem segs m a 4 (Model.e_size e) -> val_mem segs m (a + 4) 4 (Model.e_type e) ->
garr8 segs m (a + 8) (map (fun x : byte => bv_unsigned x) (Model.e_body e)) ->
(forall i, 0 <= i < Model.pad8 (Model.e_size e) ->
 mbyte segs m (a + 8 + Model.e_size e + i) = Some (Z_to_bv 8 0)) ->
garr8 segs m a (map (fun x : byte => bv_unsigned x) (Model.enc_pod e)).
Proof.
intros m a e Hl _ _ Vs Vt Gb Hz. pose proof (pwm_pad8_range (Model.e_size e)) as P.
rewrite pwm_enc_split, !map_app.
apply pwm_garr8_app. split; [apply pwm_garr8_of_val; exact Vs|].
rewrite length_map, pwm_length_le32. apply pwm_garr8_app. split.
{ replace (a + Z.of_nat 4) with (a + 4) by lia. apply pwm_garr8_of_val. exact Vt. }
rewrite length_map, pwm_length_le32. apply pwm_garr8_app. split.
{ replace (a + Z.of_nat 4 + Z.of_nat 4) with (a + 8) by lia. exact Gb. }
rewrite length_map. apply pwm_garr8_zeros. intros i Hi. rewrite Z2Nat.id in Hi by lia.
replace (a + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat (length (Model.e_body e)) + i)
with (a + 8 + Model.e_size e + i) by lia.
apply Hz. exact Hi.
Qed.

End m.

Print Assumptions pwm_byte_range.
Print Assumptions pwm_unsigned_byte.
Print Assumptions pwm_le_byte_range.
Print Assumptions pwm_le_byte_1.
Print Assumptions pwm_le_byte_bv.
Print Assumptions pwm_nth_le_shiftr.
Print Assumptions pwm_le_bytes_nth.
Print Assumptions pwm_nth_map.
Print Assumptions pwm_nth_repeat.
Print Assumptions pwm_length_le32.
Print Assumptions pwm_length_zeros.
Print Assumptions pwm_le32_nth.
Print Assumptions pwm_pad8_range.
Print Assumptions pwm_pad8_mod.
Print Assumptions pwm_byte_val.
Print Assumptions pwm_garr8_field.
Print Assumptions pwm_garr8_of_bytes.
Print Assumptions pwm_garr8_app.
Print Assumptions pwm_garr8_of_val.
Print Assumptions pwm_val_of_garr8.
Print Assumptions pwm_garr8_zeros.
Print Assumptions pwm_aview_mbyte.
Print Assumptions pwm_mbyte_kept.
Print Assumptions pwm_garr8_kept.
Print Assumptions pwm_val_mem_kept.
Print Assumptions pwm_ra_kept.
Print Assumptions pwm_hull_kept.
Print Assumptions pwm_hull_kept_eq.
Print Assumptions pwm_ent_len_eq.
Print Assumptions pwm_ent_len.
Print Assumptions pwm_ent_nth_type.
Print Assumptions pwm_ent_nth_size.
Print Assumptions pwm_ent_type.
Print Assumptions pwm_ent_size.
Print Assumptions pwm_ent_body.
Print Assumptions pwm_enc_split.
Print Assumptions pwm_enc_len.
Print Assumptions pwm_enc_of_parts.
