(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge Mem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma znth_nonneg_nth : forall l i, 0 <= i -> znth l i = nth (Z.to_nat i) l 0.
Proof. intros l i Hi. unfold znth. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma zlist_ext : forall (l1 l2 : list Z), length l1 = length l2 ->
  (forall i, 0 <= i < Z.of_nat (length l1) -> znth l1 i = znth l2 i) -> l1 = l2.
Proof.
  intros l1 l2 HL HE. apply (nth_ext l1 l2 0 0 HL). intros n Hn.
  specialize (HE (Z.of_nat n) ltac:(lia)). rewrite !znth_nonneg_nth, !Nat2Z.id in HE by lia. exact HE.
Qed.

Lemma znth_app : forall (l1 l2 : list Z) i, 0 <= i ->
  znth (l1 ++ l2) i = if i <? Z.of_nat (length l1) then znth l1 i else znth l2 (i - Z.of_nat (length l1)).
Proof.
  intros l1 l2 i Hi. destruct (Z.ltb_spec i (Z.of_nat (length l1))); rewrite !znth_nonneg_nth by lia.
  - apply app_nth1. lia.
  - rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma nth_firstn_any : forall (l : list Z) k i, (i < k)%nat -> nth i (firstn k l) 0 = nth i l 0.
Proof.
  intros l k i Hik. revert l k Hik. induction i as [|i IH]; intros l k Hik.
  - destruct k; [lia|]. destruct l; reflexivity.
  - destruct k; [lia|]. destruct l; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma znth_zfirstn : forall n (l : list Z) i, 0 <= i < n -> znth (zfirstn n l) i = znth l i.
Proof. intros n l i Hi. rewrite !znth_nonneg_nth by lia. unfold zfirstn. apply nth_firstn_any. lia. Qed.

Lemma znth_zskipn : forall n (l : list Z) i, 0 <= n -> 0 <= i -> znth (zskipn n l) i = znth l (n + i).
Proof. intros n l i Hn Hi. rewrite !znth_nonneg_nth by lia. unfold zskipn. rewrite nth_skipn. f_equal. lia. Qed.

Lemma znth_over : forall (l : list Z) i, Z.of_nat (length l) <= i -> znth l i = 0.
Proof. intros l i Hi. rewrite znth_nonneg_nth by lia. apply nth_overflow. lia. Qed.

Lemma zfirstn_length_le : forall n (l : list Z), 0 <= n <= Z.of_nat (length l) -> length (zfirstn n l) = Z.to_nat n.
Proof. intros. unfold zfirstn. rewrite length_firstn. lia. Qed.
Lemma zskipn_length : forall n (l : list Z), length (zskipn n l) = (length l - Z.to_nat n)%nat.
Proof. intros. unfold zskipn. apply length_skipn. Qed.

(* [comment removed for export] *)
Lemma znth_buf_write_at : forall off l d i, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) -> 0 <= i ->
  znth (buf_write_at off l d) i =
  if (off <=? i) && (i <? off + Z.of_nat (length l)) then znth l (i - off) else znth d i.
Proof.
  intros off l d i Ho Hl Hi. unfold buf_write_at, zlength.
  rewrite znth_app by lia. rewrite zfirstn_length_le by lia.
  destruct (Z.ltb_spec i (Z.of_nat (Z.to_nat off))).
  - replace (off <=? i) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb]. apply znth_zfirstn. lia.
  - replace (off <=? i) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    rewrite znth_app by lia. destruct (Z.ltb_spec (i - Z.of_nat (Z.to_nat off)) (Z.of_nat (length l))).
    + replace (i <? off + Z.of_nat (length l)) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. lia.
    + replace (i <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite znth_zskipn by lia. f_equal. lia.
Qed.

Lemma znth_zslice : forall off n (d : list Z) j, 0 <= off -> 0 <= j < n ->
  znth (zslice off n d) j = znth d (off + j).
Proof. intros. unfold zslice. rewrite znth_zfirstn by lia. apply znth_zskipn; lia. Qed.

Lemma znth_rev : forall (l : list Z) j, 0 <= j < Z.of_nat (length l) -> znth (rev l) j = znth l (Z.of_nat (length l) - 1 - j).
Proof.
  intros l j Hj. rewrite !znth_nonneg_nth by lia.
  rewrite rev_nth by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_u8_write_other : forall off l d j, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + Z.of_nat (length l) <= j) ->
  get_u8 (buf_write_at off l d) j = get_u8 d j.
Proof.
  intros off l d j Ho Hl Hj Hd. unfold get_u8. rewrite znth_buf_write_at by lia.
  destruct Hd; [replace (off <=? j) with false by (symmetry; apply Z.leb_gt; lia)
              | replace (j <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia); rewrite Bool.andb_false_r];
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zslice_write_other : forall off l d a n, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  0 <= a -> 0 <= n -> a + n <= Z.of_nat (length d) ->
  (a + n <= off \/ off + Z.of_nat (length l) <= a) ->
  zslice a n (buf_write_at off l d) = zslice a n d.
Proof.
  intros off l d a n Ho Hl Ha Hn Han Hd.
  apply zlist_ext.
  - rewrite !zslice_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite zslice_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite !znth_zslice by lia. rewrite znth_buf_write_at by lia.
    destruct Hd.
    + replace (off <=? a + i) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    + replace (a + i <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zslice_write_same : forall off l d, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  zslice off (Z.of_nat (length l)) (buf_write_at off l d) = l.
Proof.
  intros off l d Ho Hl. apply zlist_ext.
  - rewrite zslice_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite zslice_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite znth_zslice by lia. rewrite znth_buf_write_at by lia.
    replace (off <=? off + i) with true by (symmetry; apply Z.leb_le; lia).
    replace (off + i <? off + Z.of_nat (length l)) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. f_equal. lia.
Qed.

Lemma get_u8_swap_other : forall k off d j, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + k <= j) -> get_u8 (swap_field k off d) j = get_u8 d j.
Proof.
  intros k off d j Ho Hk Hl Hj Hd. unfold swap_field.
  apply get_u8_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_le32_swap_other : forall k off d a, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= a -> a + 4 <= Z.of_nat (length d) ->
  (a + 4 <= off \/ off + k <= a) -> get_le32 (swap_field k off d) a = get_le32 d a.
Proof.
  intros k off d a Ho Hk Hl Ha Ha4 Hd. unfold get_le32, swap_field. f_equal.
  apply zslice_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_le16_swap_other : forall k off d a, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= a -> a + 2 <= Z.of_nat (length d) ->
  (a + 2 <= off \/ off + k <= a) -> get_le16 (swap_field k off d) a = get_le16 d a.
Proof.
  intros k off d a Ho Hk Hl Ha Ha2 Hd. unfold get_le16, swap_field. f_equal.
  apply zslice_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_u8_write_other' : forall off l d j n, length l = n -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + Z.of_nat n <= j) -> get_u8 (buf_write_at off l d) j = get_u8 d j.
Proof. intros off l d j n <-. apply get_u8_write_other. Qed.

(* [comment removed for export] *)
Lemma get_le32_write_same : forall off d y0 y1 y2 y3, 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  get_le32 (buf_write_at off [y0; y1; y2; y3] d) off = y0 + 256 * y1 + 65536 * y2 + 16777216 * y3.
Proof.
  intros off d y0 y1 y2 y3 Ho Hl. unfold get_le32.
  pose proof (zslice_write_same off [y0; y1; y2; y3] d Ho ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [y0; y1; y2; y3])) with 4 in E.
  rewrite E. cbn. lia.
Qed.
Lemma get_le16_write_same : forall off d y0 y1, 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  get_le16 (buf_write_at off [y0; y1] d) off = y0 + 256 * y1.
Proof.
  intros off d y0 y1 Ho Hl. unfold get_le16.
  pose proof (zslice_write_same off [y0; y1] d Ho ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [y0; y1])) with 2 in E.
  rewrite E. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma buf_write_at_comm : forall o1 l1 o2 l2 d, 0 <= o1 -> 0 <= o2 ->
  o1 + Z.of_nat (length l1) <= Z.of_nat (length d) -> o2 + Z.of_nat (length l2) <= Z.of_nat (length d) ->
  (o1 + Z.of_nat (length l1) <= o2 \/ o2 + Z.of_nat (length l2) <= o1) ->
  buf_write_at o2 l2 (buf_write_at o1 l1 d) = buf_write_at o1 l1 (buf_write_at o2 l2 d).
Proof.
  intros o1 l1 o2 l2 d H1 H2 L1 L2 D. apply zlist_ext.
  - rewrite !buf_write_at_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite !buf_write_at_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite !znth_buf_write_at by (rewrite ?buf_write_at_length; lia).
    destruct (Z.leb_spec o2 i); destruct (Z.ltb_spec i (o2 + Z.of_nat (length l2)));
    destruct (Z.leb_spec o1 i); destruct (Z.ltb_spec i (o1 + Z.of_nat (length l1))); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma swap8_split : forall off off4 d x0 x1 x2 x3 x4 x5 x6 x7, 0 <= off -> off + 8 <= Z.of_nat (length d) -> off4 = off + 4 ->
  zslice off 4 d = [x0; x1; x2; x3] -> zslice off4 4 d = [x4; x5; x6; x7] ->
  buf_write_at off4 [x3; x2; x1; x0] (buf_write_at off [x7; x6; x5; x4] d) = swap_field 8 off d.
Proof.
  intros off off4 d x0 x1 x2 x3 x4 x5 x6 x7 Ho Hl -> E0 E1.
  pose proof (get_u8_of_slice4 off d _ _ _ _ Ho ltac:(lia) E0) as (A0 & A1 & A2 & A3).
  pose proof (get_u8_of_slice4 (off + 4) d _ _ _ _ ltac:(lia) ltac:(lia) E1) as (A4 & A5 & A6 & A7). unfold get_u8 in *.
  unfold swap_field. apply zlist_ext.
  - rewrite !buf_write_at_length; cbn [length]; rewrite ?buf_write_at_length, ?length_rev, ?zslice_length; cbn [length]; lia.
  - intros i Hi. rewrite !buf_write_at_length in Hi by (cbn [length]; rewrite ?buf_write_at_length; cbn [length]; lia).
    rewrite !znth_buf_write_at by (cbn [length]; rewrite ?buf_write_at_length, ?length_rev, ?zslice_length; cbn [length]; lia).
    cbn [length]. rewrite length_rev, zslice_length by lia.
    destruct (Z.leb_spec (off + 4) i); destruct (Z.ltb_spec i (off + 4 + Z.of_nat 4));
    destruct (Z.leb_spec off i); destruct (Z.ltb_spec i (off + Z.of_nat 4)); destruct (Z.ltb_spec i (off + Z.of_nat (Z.to_nat 8)));
    cbn [andb]; try reflexivity; try lia.
    + rewrite znth_rev by (rewrite zslice_length; lia). rewrite zslice_length by lia. rewrite znth_zslice by lia.
      assert (C : i - (off + 4) = 0 \/ i - (off + 4) = 1 \/ i - (off + 4) = 2 \/ i - (off + 4) = 3) by lia.
      destruct C as [C|[C|[C|C]]]; rewrite C; cbn -[Z.add Z.sub Z.of_nat];
      [rewrite <- A3 | rewrite <- A2 | rewrite <- A1 | rewrite <- A0]; f_equal; lia.
    + rewrite znth_rev by (rewrite zslice_length; lia). rewrite zslice_length by lia. rewrite znth_zslice by lia.
      assert (C : i - off = 0 \/ i - off = 1 \/ i - off = 2 \/ i - off = 3) by lia.
      destruct C as [C|[C|[C|C]]]; rewrite C; cbn -[Z.add Z.sub Z.of_nat];
      [rewrite <- A7 | rewrite <- A6 | rewrite <- A5 | rewrite <- A4]; f_equal; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_of_lanes : forall E y0 y1 y2 y3,
  E mod 2^32 = y0 + 256 * y1 + 65536 * y2 + 16777216 * y3 ->
  0 <= y0 < 256 -> 0 <= y1 < 256 -> 0 <= y2 < 256 -> 0 <= y3 < 256 ->
  le4 (Z_to_bv 64 E) = zbytes [y0; y1; y2; y3].
Proof.
  intros E y0 y1 y2 y3 HE H0 H1 H2 H3. apply le4_of_mod32; [reflexivity|].
  cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^32 * 2^32). change (bv_modulus 8) with 256.
  rewrite Z.rem_mul_r, HE by lia. rewrite !(Z.mod_small _ 256) by lia. lia.
Qed.
Lemma le2_of_lanes : forall E y0 y1,
  E mod 2^16 = y0 + 256 * y1 -> 0 <= y0 < 256 -> 0 <= y1 < 256 ->
  le2 (Z_to_bv 64 E) = zbytes [y0; y1].
Proof.
  intros E y0 y1 HE H0 H1. apply le2_of_mod16; [reflexivity|].
  cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^16 * 2^48). change (bv_modulus 8) with 256.
  rewrite Z.rem_mul_r, HE by lia. rewrite !(Z.mod_small _ 256) by lia. lia.
Qed.

(* [comment removed for export] *)
Definition bytes_ok (L : list Z) : Prop := Forall (fun x => 0 <= x < 256) L.

Lemma le_of_bytes_range : forall L, bytes_ok L -> 0 <= le_of_bytes L < 256 ^ (Z.of_nat (length L)).
Proof.
  induction L as [|x L IH]; intros HB; cbn [le_of_bytes length].
  - lia.
  - apply Forall_cons_iff in HB as [Hx HB]. specialize (IH HB). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma le_of_bytes_app : forall L1 L2, le_of_bytes (L1 ++ L2) = le_of_bytes L1 + 256 ^ (Z.of_nat (length L1)) * le_of_bytes L2.
Proof.
  induction L1 as [|x L1 IH]; intros L2; cbn [le_of_bytes app length].
  - lia.
  - rewrite IH. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma le_of_bytes_repeat0 : forall k L, le_of_bytes (repeat 0 k ++ L) = 256 ^ (Z.of_nat k) * le_of_bytes L.
Proof.
  intros k L. rewrite le_of_bytes_app, repeat_length.
  replace (le_of_bytes (repeat 0 k)) with 0; [lia|]. induction k; cbn; lia.
Qed.

Lemma bytes_ok_firstn : forall n L, bytes_ok L -> bytes_ok (firstn n L).
Proof. intros. unfold bytes_ok. rewrite <- (firstn_skipn n L) in H. apply Forall_app in H. tauto. Qed.
Lemma bytes_ok_skipn : forall n L, bytes_ok L -> bytes_ok (skipn n L).
Proof. intros. unfold bytes_ok. rewrite <- (firstn_skipn n L) in H. apply Forall_app in H. tauto. Qed.

Lemma le_of_bytes_split : forall n L, le_of_bytes L = le_of_bytes (firstn n L) + 256 ^ (Z.of_nat (length (firstn n L))) * le_of_bytes (skipn n L).
Proof. intros n L. rewrite <- (firstn_skipn n L) at 1. apply le_of_bytes_app. Qed.

(* [comment removed for export] *)
Lemma lanes_mod : forall n L, bytes_ok L -> le_of_bytes L mod 256 ^ (Z.of_nat n) = le_of_bytes (firstn n L).
Proof.
  intros n L HB. rewrite (le_of_bytes_split n L).
  pose proof (le_of_bytes_range (firstn n L) (bytes_ok_firstn n L HB)) as R.
  destruct (Nat.le_gt_cases (length L) n).
  - rewrite firstn_all2, skipn_all2 by lia. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r.
    apply Z.mod_small. pose proof (le_of_bytes_range L HB). rewrite firstn_all2 in R by lia.
    assert (256 ^ Z.of_nat (length L) <= 256 ^ Z.of_nat n) by (apply Z.pow_le_mono_r; lia). lia.
  - rewrite length_firstn in *. rewrite Nat.min_l in * by lia.
    set (A := le_of_bytes (firstn n L)) in *. set (B := le_of_bytes (skipn n L)) in *. set (P := 256 ^ Z.of_nat n) in *.
    replace (A + P * B) with (A + B * P) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma lanes_mod64 : forall L, bytes_ok L -> le_of_bytes L mod 18446744073709551616 = le_of_bytes (firstn 8 L).
Proof. intros. change 18446744073709551616 with (256 ^ Z.of_nat 8). apply lanes_mod. assumption. Qed.
Lemma lanes_mod32 : forall L, bytes_ok L -> le_of_bytes L mod 2^32 = le_of_bytes (firstn 4 L).
Proof. intros. change (2^32) with (256 ^ Z.of_nat 4). apply lanes_mod. assumption. Qed.
Lemma lanes_mod16 : forall L, bytes_ok L -> le_of_bytes L mod 2^16 = le_of_bytes (firstn 2 L).
Proof. intros. change (2^16) with (256 ^ Z.of_nat 2). apply lanes_mod. assumption. Qed.
Lemma lanes_wrap32 : forall L, bytes_ok L -> bv_wrap 32 (le_of_bytes L) = le_of_bytes (firstn 4 L).
Proof. intros. rewrite bv_wrap32_eq. apply lanes_mod32. assumption. Qed.

(* [comment removed for export] *)
Lemma lanes_shl : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  (Z.shiftl (le_of_bytes L) n) mod 18446744073709551616 = le_of_bytes (firstn 8 (repeat 0 k ++ L)).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite <- lanes_mod64 by (unfold bytes_ok; apply Forall_app; split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia| exact HB]).
  rewrite le_of_bytes_repeat0. rewrite Z.pow_mul_r by lia. change (2^8) with 256. f_equal. lia.
Qed.
Lemma lanes_shl_nomod : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  Z.shiftl (le_of_bytes L) n = le_of_bytes (repeat 0 k ++ L).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia. rewrite le_of_bytes_repeat0. rewrite Z.pow_mul_r by lia.
  change (2^8) with 256. lia.
Qed.
Lemma lanes_shr : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  Z.shiftr (le_of_bytes L) n = le_of_bytes (skipn k L).
Proof.
  intros k L n HB ->. rewrite Z.shiftr_div_pow2 by lia. rewrite (le_of_bytes_split k L) at 1.
  pose proof (le_of_bytes_range (firstn k L) (bytes_ok_firstn k L HB)) as R.
  destruct (Nat.le_gt_cases (length L) k).
  - rewrite firstn_all2, skipn_all2 by lia. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r. apply Z.div_small.
    rewrite firstn_all2 in R by lia. rewrite Z.pow_mul_r by lia. change (2^8) with 256.
    assert (256 ^ Z.of_nat (length L) <= 256 ^ Z.of_nat k) by (apply Z.pow_le_mono_r; lia). lia.
  - rewrite length_firstn in *. rewrite Nat.min_l in * by lia. rewrite Z.pow_mul_r by lia. change (2^8) with 256.
    set (A := le_of_bytes (firstn k L)) in *. set (B := le_of_bytes (skipn k L)) in *. set (P := 256 ^ Z.of_nat k) in *.
    replace (A + P * B) with (B * P + A) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma lanes_mask : forall j L, bytes_ok L ->
  Z.land (le_of_bytes L) (255 * 2 ^ (8 * Z.of_nat j)) = le_of_bytes (repeat 0 j ++ [nth j L 0]).
Proof.
  intros j L HB. rewrite land_mask8 by (pose proof (le_of_bytes_range L HB); lia).
  rewrite le_of_bytes_repeat0. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r.
  rewrite <- Z.shiftr_div_pow2 by lia. rewrite (lanes_shr j L) by (auto; lia).
  rewrite Z.pow_mul_r by lia. change (2^8) with 256. rewrite Z.mul_comm. f_equal.
  pose proof (bytes_ok_skipn j L HB) as HS.
  destruct (skipn j L) as [|y R] eqn:E.
  - cbn. rewrite nth_overflow; [reflexivity|]. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - apply Forall_cons_iff in HS as [Hy HR]. cbn [le_of_bytes].
    replace (y + 256 * le_of_bytes R) with (y + le_of_bytes R * 256) by lia. rewrite Z.mod_add, Z.mod_small by lia.
    replace y with (nth 0 (skipn j L) 0) by (rewrite E; reflexivity). rewrite nth_skipn. f_equal. lia.
Qed.
Lemma lanes_mask1 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 65280 = le_of_bytes [0; nth 1 L 0].
Proof. intros. change 65280 with (255 * 2 ^ (8 * Z.of_nat 1)). rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask2 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 16711680 = le_of_bytes [0; 0; nth 2 L 0].
Proof. intros. change 16711680 with (255 * 2 ^ (8 * Z.of_nat 2)). rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask0 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 255 = le_of_bytes [nth 0 L 0].
Proof. intros. change 255 with (255 * 2 ^ (8 * Z.of_nat 0)) at 1. rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask3 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 4278190080 = le_of_bytes [0; 0; 0; nth 3 L 0].
Proof. intros. change 4278190080 with (255 * 2 ^ (8 * Z.of_nat 3)). rewrite lanes_mask by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint lanes_merge (L1 L2 L : list Z) : Prop :=
  match L1, L2, L with
  | [], l2, l => l = l2
  | l1, [], l => l = l1
  | a :: l1, b :: l2, c :: l => ((a = 0 /\ c = b) \/ (b = 0 /\ c = a)) /\ lanes_merge l1 l2 l
  | _ :: _, _ :: _, [] => False
  end.
Lemma lor_shift8 : forall a b c d, 0 <= a < 256 -> 0 <= c < 256 -> 0 <= b -> 0 <= d -> (a = 0 \/ c = 0) ->
  Z.lor (a + 256 * b) (c + 256 * d) = (Z.lor a c) + 256 * Z.lor b d.
Proof.
  intros a b c d Ha Hc Hb Hd Hz.
  assert (E1 : a + 256 * b = Z.lor (256 * b) a).
  { rewrite (lor_add (256 * b) a 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia]. }
  assert (E2 : c + 256 * d = Z.lor (256 * d) c).
  { rewrite (lor_add (256 * d) c 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia]. }
  rewrite E1, E2.
  transitivity (Z.lor (Z.lor (256 * b) (256 * d)) (Z.lor a c)).
  { rewrite <- !Z.lor_assoc. f_equal. rewrite (Z.lor_comm a (Z.lor (256 * d) c)). rewrite <- Z.lor_assoc. f_equal. apply Z.lor_comm. }
  assert (R : 0 <= Z.lor a c < 256).
  { destruct Hz as [-> | ->]; [rewrite Z.lor_0_l | rewrite Z.lor_0_r]; lia. }
  replace (Z.lor (256 * b) (256 * d)) with (256 * Z.lor b d).
  2:{ rewrite !(Z.mul_comm 256). change 256 with (2^8). rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_lor. reflexivity. }
  pose proof (Z.lor_nonneg b d).
  rewrite (lor_add (256 * Z.lor b d) (Z.lor a c) 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia].
Qed.
Lemma lanes_lor : forall L1 L2 L, lanes_merge L1 L2 L -> bytes_ok L1 -> bytes_ok L2 ->
  Z.lor (le_of_bytes L1) (le_of_bytes L2) = le_of_bytes L.
Proof.
  induction L1 as [|a L1 IH]; intros L2 L HM H1 H2.
  - cbn in HM. subst L. cbn [le_of_bytes]. apply Z.lor_0_l.
  - destruct L2 as [|b L2].
    + cbn in HM. subst L. apply Z.lor_0_r.
    + destruct L as [|c L]; [destruct HM|]. cbn [lanes_merge] in HM. destruct HM as [Hc HM].
      apply Forall_cons_iff in H1 as [Ha H1]. apply Forall_cons_iff in H2 as [Hb H2].
      cbn [le_of_bytes]. pose proof (le_of_bytes_range L1 H1). pose proof (le_of_bytes_range L2 H2).
      rewrite lor_shift8 by lia. rewrite (IH L2 L) by assumption. f_equal.
      destruct Hc as [[-> ->]|[-> ->]]; [apply Z.lor_0_l | apply Z.lor_0_r].
Qed.

(* [comment removed for export] *)
Definition sx_lane (x3 : Z) : Z := if x3 <? 128 then 0 else 255.
Lemma sx_lane_range : forall x, 0 <= sx_lane x < 256.
Proof. intros. unfold sx_lane. destruct (x <? 128); lia. Qed.
Lemma lanes_sx32 : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [x0; x1; x2; x3]))) =
  le_of_bytes [x0; x1; x2; x3; sx_lane x3; sx_lane x3; sx_lane x3; sx_lane x3].
Proof.
  intros. cbn [le_of_bytes]. rewrite unsigned_sx32 by lia. unfold sx_lane.
  destruct (Z.ltb_spec x3 128); destruct (Z.ltb_spec (x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * 0)))) (2^31)); lia.
Qed.
(* [comment removed for export] *)
Lemma lanes_swrap_small : forall L, bytes_ok L -> (length L <= 3)%nat ->
  (bv_swrap 32 (le_of_bytes L)) mod 18446744073709551616 = le_of_bytes L.
Proof.
  intros L HB HL. pose proof (le_of_bytes_range L HB) as R.
  assert (256 ^ Z.of_nat (length L) <= 256 ^ 3) by (apply Z.pow_le_mono_r; lia).
  rewrite swrap32_small by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma lanes_swrap4 : forall a b c e, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= e < 256 ->
  (bv_swrap 32 (le_of_bytes [a; b; c; e])) mod 18446744073709551616 =
  le_of_bytes [a; b; c; e; sx_lane e; sx_lane e; sx_lane e; sx_lane e].
Proof.
  intros. cbn [le_of_bytes]. rewrite bv_swrap32_eq. unfold sx_lane.
  destruct (Z.ltb_spec e 128); Z.div_mod_to_equations; lia.
Qed.
Lemma lanes_swrap_any : forall L, bytes_ok L -> (4 < length L)%nat ->
  bv_swrap 32 (le_of_bytes L) = bv_swrap 32 (le_of_bytes (firstn 4 L)).
Proof.
  intros L HB HL. rewrite !bv_swrap32_eq. rewrite <- (lanes_mod32 L HB). Z.div_mod_to_equations. lia.
Qed.
Lemma lanes_swrap_shl : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  bv_swrap 32 (Z.shiftl (le_of_bytes L) n) = bv_swrap 32 (le_of_bytes (firstn 4 (repeat 0 k ++ L))).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia.
  assert (HB' : bytes_ok (repeat 0 k ++ L)).
  { unfold bytes_ok. apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia| exact HB]. }
  replace (le_of_bytes L * 2 ^ (8 * Z.of_nat k)) with (le_of_bytes (repeat 0 k ++ L))
    by (rewrite le_of_bytes_repeat0, Z.pow_mul_r by lia; change (2^8) with 256; lia).
  rewrite !bv_swrap32_eq. rewrite <- (lanes_mod32 _ HB'). Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ltu_lit_sx32 : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 ->
  bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = (k <? x).
Proof.
  intros k x Hx Hk. rewrite bv_ltu_Z, unsigned_sx32, (unsigned_lit k) by lia.
  destruct (Z.ltb_spec x (2^31)); destruct (Z.ltb_spec k x); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.
Lemma ltu_lit_sx32_falseZ : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x <= k -> bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = false.
Proof. intros. rewrite ltu_lit_sx32 by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_lit_sx32_trueZ : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k < x -> bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = true.
Proof. intros. rewrite ltu_lit_sx32 by lia. apply Z.ltb_lt. lia. Qed.
(* [comment removed for export] *)
Lemma sx32_as_swrap : forall x, sx32 (Z_to_bv 64 x) = Z_to_bv 64 (bv_swrap 32 x).
Proof.
  intros x. unfold sx32. rewrite unsigned_lit_wrap. f_equal. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_swrap_swrap : forall x y, bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x mod 2^32 <? y mod 2^32).
Proof.
  intros x y. rewrite bv_ltu_Z, !unsigned_swrap32.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound y (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (y mod 2^32) (2^31)); cbv iota;
    (destruct (Z.ltb_spec (x mod 2^32) (y mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia])).
Qed.
Lemma eqb_swrap_swrap : forall x y, bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x mod 2^32 =? y mod 2^32).
Proof.
  intros x y. unfold bv_eqb. rewrite !unsigned_swrap32.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound y (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (y mod 2^32) (2^31)); cbv iota;
    (destruct (Z.eqb_spec (x mod 2^32) (y mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
Lemma eqb_swrap_small : forall x k, 0 <= k < 2^31 -> bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 =? k).
Proof.
  intros x k Hk. unfold bv_eqb. rewrite unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.eqb_spec (x mod 2^32) k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
Lemma eqb_small_swrap : forall k x, 0 <= k < 2^31 -> bv_eqb (Z_to_bv 64 k) (Z_to_bv 64 (bv_swrap 32 x)) = (k =? x mod 2^32).
Proof.
  intros k x Hk. unfold bv_eqb. rewrite unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.eqb_spec k (x mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
(* [comment removed for export] *)
Lemma ltu_swrap_small : forall x k, 0 <= k < 2^31 -> bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 <? k).
Proof. intros. apply ltu_swrap_lit. lia. Qed.
Lemma ltu_small_swrap : forall k x, 0 <= k < 2^31 -> bv_ltu (Z_to_bv 64 k) (Z_to_bv 64 (bv_swrap 32 x)) = (k <? x mod 2^32).
Proof.
  intros k x Hk. rewrite bv_ltu_Z, unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.ltb_spec k (x mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia])).
Qed.

Ltac bytes_ok_tac := unfold bytes_ok; repeat (apply Forall_cons; [fastfirst (first [assumption | apply sx_lane_range | lia]) |]); apply Forall_nil.

(* [comment removed for export] *)
Ltac lanes_merge_compute L1 L2 :=
  lazymatch L1 with
  | [] => L2
  | ?a :: ?l1 =>
    lazymatch L2 with
    | [] => L1
    | ?b :: ?l2 =>
      let r := lanes_merge_compute l1 l2 in
      lazymatch a with
      | 0 => constr:(b :: r)
      | _ => lazymatch b with 0 => constr:(a :: r) end
      end
    end
  end.
Ltac lanes_merge_tac := cbn [lanes_merge]; repeat split; try reflexivity;
  first [ left; split; reflexivity | right; split; reflexivity ].

(* [comment removed for export] *)
Ltac lanes_step :=
  match goal with
  | |- context [ (Z.shiftl (le_of_bytes ?L) ?n) mod 18446744073709551616 ] =>
      let k := eval cbv -[sx_lane] in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (firstn 8 (repeat 0 k ++ L)) in
      replace ((Z.shiftl (le_of_bytes L) n) mod 18446744073709551616) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shl k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.shiftl (le_of_bytes ?L) ?n ] =>
      let k := eval cbv in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (repeat 0 k ++ L) in
      replace (Z.shiftl (le_of_bytes L) n) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shl_nomod k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.shiftr (le_of_bytes ?L) ?n ] =>
      let k := eval cbv -[sx_lane] in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (skipn k L) in
      replace (Z.shiftr (le_of_bytes L) n) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shr k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.land (le_of_bytes ?L) 65280 ] =>
      let y := eval cbv -[sx_lane] in (nth 1 L 0) in
      replace (Z.land (le_of_bytes L) 65280) with (le_of_bytes [0; y]) by (symmetry; apply (lanes_mask1 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 16711680 ] =>
      let y := eval cbv -[sx_lane] in (nth 2 L 0) in
      replace (Z.land (le_of_bytes L) 16711680) with (le_of_bytes [0; 0; y]) by (symmetry; apply (lanes_mask2 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 4278190080 ] =>
      let y := eval cbv -[sx_lane] in (nth 3 L 0) in
      replace (Z.land (le_of_bytes L) 4278190080) with (le_of_bytes [0; 0; 0; y]) by (symmetry; apply (lanes_mask3 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 255 ] =>
      let y := eval cbv -[sx_lane] in (nth 0 L 0) in
      replace (Z.land (le_of_bytes L) 255) with (le_of_bytes [y]) by (symmetry; apply (lanes_mask0 L); bytes_ok_tac)
  | |- context [ bv_wrap 32 (le_of_bytes ?L) ] =>
      let L2 := eval cbv -[sx_lane] in (firstn 4 L) in
      replace (bv_wrap 32 (le_of_bytes L)) with (le_of_bytes L2) by (symmetry; apply (lanes_wrap32 L); bytes_ok_tac)
  | |- context [ (le_of_bytes ?L) mod 18446744073709551616 ] =>
      let L2 := eval cbv -[sx_lane] in (firstn 8 L) in
      replace ((le_of_bytes L) mod 18446744073709551616) with (le_of_bytes L2) by (symmetry; apply (lanes_mod64 L); bytes_ok_tac)
  | |- context [ (bv_swrap 32 (le_of_bytes [?a; ?b; ?e; ?f])) mod 18446744073709551616 ] =>
      rewrite (lanes_swrap4 a b e f) by (fastfirst (first [assumption | apply sx_lane_range | lia]))
  | |- context [ bv_swrap 32 (Z.shiftl (le_of_bytes ?L) ?n) ] =>
      let k := eval cbv in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (firstn 4 (repeat 0 k ++ L)) in
      replace (bv_swrap 32 (Z.shiftl (le_of_bytes L) n)) with (bv_swrap 32 (le_of_bytes L2))
        by (symmetry; apply (lanes_swrap_shl k L n); [bytes_ok_tac | reflexivity])
  | |- context [ bv_swrap 32 (le_of_bytes (?a :: ?b :: ?e :: ?f :: _ :: _)) ] =>
      lazymatch goal with |- context [ bv_swrap 32 (le_of_bytes ?L) ] =>
        let L2 := eval cbv -[sx_lane] in (firstn 4 L) in
        replace (bv_swrap 32 (le_of_bytes L)) with (bv_swrap 32 (le_of_bytes L2))
          by (symmetry; apply (lanes_swrap_any L); [bytes_ok_tac | cbn; lia]) end
  | |- context [ (bv_swrap 32 (le_of_bytes ?L)) mod 18446744073709551616 ] =>
      replace ((bv_swrap 32 (le_of_bytes L)) mod 18446744073709551616) with (le_of_bytes L)
        by (symmetry; apply (lanes_swrap_small L); [bytes_ok_tac | cbn; lia])
  | |- context [ Z.lor (le_of_bytes ?L1) (le_of_bytes ?L2) ] =>
      let L := lanes_merge_compute L1 L2 in
      replace (Z.lor (le_of_bytes L1) (le_of_bytes L2)) with (le_of_bytes L)
        by (symmetry; apply (lanes_lor L1 L2 L); [lanes_merge_tac | bytes_ok_tac | bytes_ok_tac])
  | |- context [ bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [?x0; ?x1; ?x2; ?x3]))) ] =>
      rewrite (lanes_sx32 x0 x1 x2 x3) by lia
  end.

(* [comment removed for export] *)
Ltac bswap_arith :=
  repeat lanes_step;
  first [ rewrite lanes_mod32 by bytes_ok_tac | rewrite lanes_mod16 by bytes_ok_tac | idtac ];
  cbn [firstn le_of_bytes]; lia.

(* [comment removed for export] *)
Example bswap_arith_ex1 : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = le_of_bytes [x0; x1; x2; x3] ->
  (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) (Z.land ((Z.shiftl X 8) mod 18446744073709551616) 16711680))
          (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex1s : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [x0; x1; x2; x3]))) ->
  (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
         (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex2 : forall x0 x1 x2 x3 x4 x5 x6 x7 X0 X1,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  0 <= x4 < 256 -> 0 <= x5 < 256 -> 0 <= x6 < 256 -> 0 <= x7 < 256 ->
  X0 = le_of_bytes [x0; x1; x2; x3] -> X1 = le_of_bytes [x4; x5; x6; x7] ->
  (Z.shiftr (Z.lor (Z.lor ((Z.shiftl X0 56) mod 18446744073709551616) ((Z.shiftl (Z.land X0 65280) 40) mod 18446744073709551616))
       (Z.lor ((Z.shiftl (Z.land (Z.lor ((Z.shiftl X1 32) mod 18446744073709551616) X0) 16711680) 24) mod 18446744073709551616)
             ((Z.shiftl ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.lor ((Z.shiftl X1 32) mod 18446744073709551616) X0)) 24)) mod 18446744073709551616) 32) mod 18446744073709551616))) 32) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X0 X1. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex3 : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = le_of_bytes [x0; x1; x2; x3] ->
  Z.lor (Z.lor ((bv_swrap 32 (Z.shiftl X 24)) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
        (Z.lor (Z.land (Z.shiftr X 8) 65280) (Z.shiftr X 24))
  = le_of_bytes [x3; x2; x1; x0; sx_lane x0; sx_lane x0; sx_lane x0; sx_lane x0].
Proof. intros. subst X. repeat lanes_step. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap32_mod32 : forall x, bv_swrap 32 (x mod 2^32) = bv_swrap 32 x.
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_add_mod64_l : forall x y, bv_swrap 32 ((bv_swrap 32 x) mod 18446744073709551616 + y) = bv_swrap 32 (x + y).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_add_mod64_r : forall x y, bv_swrap 32 (y + (bv_swrap 32 x) mod 18446744073709551616) = bv_swrap 32 (y + x).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma Z_to_bv64_mod : forall x, Z_to_bv 64 (x mod 18446744073709551616) = Z_to_bv 64 x.
Proof. intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. apply Z.mod_mod. lia. Qed.
Lemma unsigned_RF : forall x, bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (bv_swrap 32 x) mod 18446744073709551616.
Proof. intros. rewrite unsigned_lit_wrap. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sat_idiom : forall a b,
  Z_to_bv 64 (Z.lor ((0 - Z.b2z ((bv_swrap 32 (a + b)) mod 18446744073709551616 <? (bv_swrap 32 a) mod 18446744073709551616)) mod 18446744073709551616)
                    ((bv_swrap 32 (a + b)) mod 18446744073709551616))
  = Z_to_bv 64 (bv_swrap 32 (u_int_sum (a mod 2^32) (b mod 2^32))).
Proof.
  intros a b.
  pose proof (ltu_swrap_swrap (a + b) a) as E. rewrite bv_ltu_Z, !unsigned_RF in E. rewrite E. clear E.
  unfold u_int_sum, UINT_MAX.
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound b (2^32) ltac:(lia)).
  destruct (Z.leb_spec (b mod 2^32) (2^32 - 1 - a mod 2^32)).
  - replace ((a + b) mod 2^32 <? a mod 2^32) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
    cbn [Z.b2z Z.sub]. rewrite Z.lor_0_l. rewrite Z_to_bv64_mod. f_equal.
    rewrite !bv_swrap32_eq. Z.div_mod_to_equations; lia.
  - replace ((a + b) mod 2^32 <? a mod 2^32) with true by (symmetry; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
    cbn [Z.b2z]. change ((0 - 1) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.lor_comm, Z.lor_ones_low; [apply bv_eq; vm_compute; reflexivity | |].
    + apply Z.mod_pos_bound. lia.
    + destruct (Z.eq_dec ((bv_swrap 32 (a + b)) mod 18446744073709551616) 0) as [-> | NZ]; [cbn; lia|].
      apply Z.log2_lt_pow2; [pose proof (Z.mod_pos_bound (bv_swrap 32 (a + b)) 18446744073709551616); lia|].
      change (2 ^ 64) with 18446744073709551616. apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
Lemma u_int_sum_range : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 -> 0 <= u_int_sum a b < 2^32.
Proof. intros. unfold u_int_sum, UINT_MAX. destruct (Z.leb_spec b (2^32 - 1 - a)); lia. Qed.

(* [comment removed for export] *)
Lemma zslice_length_le : forall {A} off n (d : list A), 0 <= n -> (length (zslice off n d) <= Z.to_nat n)%nat.
Proof. intros. unfold zslice, zfirstn. rewrite length_firstn. lia. Qed.
Lemma get_le32_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_le32 d k < 2^32.
Proof.
  intros d k HF. unfold get_le32.
  pose proof (le_of_bytes_range (zslice k 4 d) (zslice_range k 4 d HF)) as R.
  pose proof (zslice_length_le k 4 d ltac:(lia)) as L.
  assert (256 ^ Z.of_nat (length (zslice k 4 d)) <= 256 ^ 4) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma get_le16_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_le16 d k < 65536.
Proof.
  intros d k HF. unfold get_le16.
  pose proof (le_of_bytes_range (zslice k 2 d) (zslice_range k 2 d HF)) as R.
  pose proof (zslice_length_le k 2 d ltac:(lia)) as L.
  assert (256 ^ Z.of_nat (length (zslice k 2 d)) <= 256 ^ 2) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma get_u8_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_u8 d k < 256.
Proof.
  intros d k HF. unfold get_u8, znth. destruct (k <? 0); [lia|].
  destruct (nth_in_or_default (Z.to_nat k) d 0) as [HI | ->]; [|lia].
  rewrite Forall_forall in HF. apply HF. exact HI.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_128 : forall x, 0 <= x < 256 -> Z.land x 128 = (if x <? 128 then 0 else 128).
Proof.
  intros x Hx. change 128 with (2^7) at 1. rewrite land_single_bit by lia.
  change (2^(7+1)) with 256. change (2^7) with 128. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma signed_negZ : forall x, -2^63 <= x < 0 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 64) with 64. change (2^64 `div` 2) with (2^63). Z.div_mod_to_equations. lia.
Qed.
Lemma lts_negZ : forall x y, -2^63 <= x < 0 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. unfold bv_lts. rewrite signed_negZ, signed_small by lia. apply Z.ltb_lt. lia. Qed.
Lemma le4_swrap : forall v, le4 (Z_to_bv 64 (bv_swrap 32 v)) = le4 (Z_to_bv 64 v).
Proof.
  intros v. unfold le4. rewrite !unsigned_lit_wrap.
  rewrite <- (Z_to_le_bytes_mod 4 ((bv_swrap 32 v) mod 2^64) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (v mod 2^64) 32) by (cbn; lia). f_equal.
  rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia.
Qed.
Lemma rw_cells_ext : forall segs m A cs cs', cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' ->
  rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' EB ES WF [[_ B] W]. split; [split; [exact WF|]|].
  - rewrite <- EB. exact B.
  - rewrite <- ES. exact W.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_3 : forall v, 0 <= v -> Z.land v 3 = v mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_65532 : forall v, 0 <= v -> Z.land v 65532 = v mod 65536 - v mod 4.
Proof.
  intros v Hv.
  assert (E : Z.land v 65532 = Z.ldiff (Z.land v (Z.ones 16)) (Z.ones 2)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, !Z.land_spec.
    change 65532 with (Z.ldiff (Z.ones 16) (Z.ones 2)). rewrite Z.ldiff_spec. rewrite Bool.andb_assoc. reflexivity. }
  rewrite E, Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^16) with 65536. change (2^2) with 4. Z.div_mod_to_equations. lia.
Qed.
Lemma shlr48 : forall v, 0 <= v -> Z.shiftr ((Z.shiftl v 48) mod 18446744073709551616) 48 = v mod 65536.
Proof. intros. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_sub_mod64_l : forall x y, bv_swrap 32 ((bv_swrap 32 x) mod 18446744073709551616 - y) = bv_swrap 32 (x - y).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Lemma swap16_val : forall x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 ->
  Z.lor ((Z.shiftl (x0 + 256 * x1) 8) mod 18446744073709551616) (Z.shiftr (x0 + 256 * x1) 8) = x1 + 256 * x0 + 65536 * x1.
Proof.
  intros x0 x1 H0 H1. replace (x0 + 256 * x1) with (le_of_bytes [x0; x1]) by (cbn; lia).
  repeat lanes_step. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma tlv_pair : forall p p2 d x0 x1 x2 x3, 0 <= p -> p + 4 <= Z.of_nat (length d) -> p2 = p + 2 ->
  zslice p 2 d = [x0; x1] -> zslice p2 2 d = [x2; x3] ->
  buf_write_at p2 [x3; x2] (buf_write_at p [x1; x0] d) = swap_field 2 p (swap_field 2 p2 d).
Proof.
  intros p p2 d x0 x1 x2 x3 Hp Hl -> E0 E1. unfold swap_field.
  rewrite E1. cbn [rev app].
  rewrite (zslice_write_other (p + 2) [x3; x2] d p 2) by (cbn [length]; lia). rewrite E0. cbn [rev app].
  apply buf_write_at_comm; cbn [length]; lia.
Qed.
Lemma tlv_pair_size : forall p p2 d x0 x1 x2 x3, 0 <= p -> p + 4 <= Z.of_nat (length d) -> p2 = p + 2 ->
  get_le16 (buf_write_at p2 [x3; x2] (buf_write_at p [x1; x0] d)) p = x1 + 256 * x0.
Proof.
  intros p p2 d x0 x1 x2 x3 Hp Hl ->. unfold get_le16.
  rewrite (zslice_write_other (p + 2) [x3; x2] _ p 2) by (cbn [length]; rewrite ?buf_write_at_length; cbn [length]; lia).
  pose proof (zslice_write_same p [x1; x0] d Hp ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [x1; x0])) with 2 in E.
  rewrite E. cbn. lia.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma znth_nonneg_nth : forall l i, 0 <= i -> znth l i = nth (Z.to_nat i) l 0.
Proof. intros l i Hi. unfold znth. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma zlist_ext : forall (l1 l2 : list Z), length l1 = length l2 ->
  (forall i, 0 <= i < Z.of_nat (length l1) -> znth l1 i = znth l2 i) -> l1 = l2.
Proof.
  intros l1 l2 HL HE. apply (nth_ext l1 l2 0 0 HL). intros n Hn.
  specialize (HE (Z.of_nat n) ltac:(lia)). rewrite !znth_nonneg_nth, !Nat2Z.id in HE by lia. exact HE.
Qed.

Lemma znth_app : forall (l1 l2 : list Z) i, 0 <= i ->
  znth (l1 ++ l2) i = if i <? Z.of_nat (length l1) then znth l1 i else znth l2 (i - Z.of_nat (length l1)).
Proof.
  intros l1 l2 i Hi. destruct (Z.ltb_spec i (Z.of_nat (length l1))); rewrite !znth_nonneg_nth by lia.
  - apply app_nth1. lia.
  - rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma nth_firstn_any : forall (l : list Z) k i, (i < k)%nat -> nth i (firstn k l) 0 = nth i l 0.
Proof.
  intros l k i Hik. revert l k Hik. induction i as [|i IH]; intros l k Hik.
  - destruct k; [lia|]. destruct l; reflexivity.
  - destruct k; [lia|]. destruct l; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma znth_zfirstn : forall n (l : list Z) i, 0 <= i < n -> znth (zfirstn n l) i = znth l i.
Proof. intros n l i Hi. rewrite !znth_nonneg_nth by lia. unfold zfirstn. apply nth_firstn_any. lia. Qed.

Lemma znth_zskipn : forall n (l : list Z) i, 0 <= n -> 0 <= i -> znth (zskipn n l) i = znth l (n + i).
Proof. intros n l i Hn Hi. rewrite !znth_nonneg_nth by lia. unfold zskipn. rewrite nth_skipn. f_equal. lia. Qed.

Lemma znth_over : forall (l : list Z) i, Z.of_nat (length l) <= i -> znth l i = 0.
Proof. intros l i Hi. rewrite znth_nonneg_nth by lia. apply nth_overflow. lia. Qed.

Lemma zfirstn_length_le : forall n (l : list Z), 0 <= n <= Z.of_nat (length l) -> length (zfirstn n l) = Z.to_nat n.
Proof. intros. unfold zfirstn. rewrite length_firstn. lia. Qed.
Lemma zskipn_length : forall n (l : list Z), length (zskipn n l) = (length l - Z.to_nat n)%nat.
Proof. intros. unfold zskipn. apply length_skipn. Qed.

(* [comment removed for export] *)
Lemma znth_buf_write_at : forall off l d i, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) -> 0 <= i ->
  znth (buf_write_at off l d) i =
  if (off <=? i) && (i <? off + Z.of_nat (length l)) then znth l (i - off) else znth d i.
Proof.
  intros off l d i Ho Hl Hi. unfold buf_write_at, zlength.
  rewrite znth_app by lia. rewrite zfirstn_length_le by lia.
  destruct (Z.ltb_spec i (Z.of_nat (Z.to_nat off))).
  - replace (off <=? i) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb]. apply znth_zfirstn. lia.
  - replace (off <=? i) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    rewrite znth_app by lia. destruct (Z.ltb_spec (i - Z.of_nat (Z.to_nat off)) (Z.of_nat (length l))).
    + replace (i <? off + Z.of_nat (length l)) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. lia.
    + replace (i <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite znth_zskipn by lia. f_equal. lia.
Qed.

Lemma znth_zslice : forall off n (d : list Z) j, 0 <= off -> 0 <= j < n ->
  znth (zslice off n d) j = znth d (off + j).
Proof. intros. unfold zslice. rewrite znth_zfirstn by lia. apply znth_zskipn; lia. Qed.

Lemma znth_rev : forall (l : list Z) j, 0 <= j < Z.of_nat (length l) -> znth (rev l) j = znth l (Z.of_nat (length l) - 1 - j).
Proof.
  intros l j Hj. rewrite !znth_nonneg_nth by lia.
  rewrite rev_nth by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_u8_write_other : forall off l d j, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + Z.of_nat (length l) <= j) ->
  get_u8 (buf_write_at off l d) j = get_u8 d j.
Proof.
  intros off l d j Ho Hl Hj Hd. unfold get_u8. rewrite znth_buf_write_at by lia.
  destruct Hd; [replace (off <=? j) with false by (symmetry; apply Z.leb_gt; lia)
              | replace (j <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia); rewrite Bool.andb_false_r];
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zslice_write_other : forall off l d a n, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  0 <= a -> 0 <= n -> a + n <= Z.of_nat (length d) ->
  (a + n <= off \/ off + Z.of_nat (length l) <= a) ->
  zslice a n (buf_write_at off l d) = zslice a n d.
Proof.
  intros off l d a n Ho Hl Ha Hn Han Hd.
  apply zlist_ext.
  - rewrite !zslice_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite zslice_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite !znth_zslice by lia. rewrite znth_buf_write_at by lia.
    destruct Hd.
    + replace (off <=? a + i) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    + replace (a + i <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zslice_write_same : forall off l d, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  zslice off (Z.of_nat (length l)) (buf_write_at off l d) = l.
Proof.
  intros off l d Ho Hl. apply zlist_ext.
  - rewrite zslice_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite zslice_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite znth_zslice by lia. rewrite znth_buf_write_at by lia.
    replace (off <=? off + i) with true by (symmetry; apply Z.leb_le; lia).
    replace (off + i <? off + Z.of_nat (length l)) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. f_equal. lia.
Qed.

Lemma get_u8_swap_other : forall k off d j, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + k <= j) -> get_u8 (swap_field k off d) j = get_u8 d j.
Proof.
  intros k off d j Ho Hk Hl Hj Hd. unfold swap_field.
  apply get_u8_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_le32_swap_other : forall k off d a, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= a -> a + 4 <= Z.of_nat (length d) ->
  (a + 4 <= off \/ off + k <= a) -> get_le32 (swap_field k off d) a = get_le32 d a.
Proof.
  intros k off d a Ho Hk Hl Ha Ha4 Hd. unfold get_le32, swap_field. f_equal.
  apply zslice_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_le16_swap_other : forall k off d a, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= a -> a + 2 <= Z.of_nat (length d) ->
  (a + 2 <= off \/ off + k <= a) -> get_le16 (swap_field k off d) a = get_le16 d a.
Proof.
  intros k off d a Ho Hk Hl Ha Ha2 Hd. unfold get_le16, swap_field. f_equal.
  apply zslice_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_u8_write_other' : forall off l d j n, length l = n -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + Z.of_nat n <= j) -> get_u8 (buf_write_at off l d) j = get_u8 d j.
Proof. intros off l d j n <-. apply get_u8_write_other. Qed.

(* [comment removed for export] *)
Lemma get_le32_write_same : forall off d y0 y1 y2 y3, 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  get_le32 (buf_write_at off [y0; y1; y2; y3] d) off = y0 + 256 * y1 + 65536 * y2 + 16777216 * y3.
Proof.
  intros off d y0 y1 y2 y3 Ho Hl. unfold get_le32.
  pose proof (zslice_write_same off [y0; y1; y2; y3] d Ho ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [y0; y1; y2; y3])) with 4 in E.
  rewrite E. cbn. lia.
Qed.
Lemma get_le16_write_same : forall off d y0 y1, 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  get_le16 (buf_write_at off [y0; y1] d) off = y0 + 256 * y1.
Proof.
  intros off d y0 y1 Ho Hl. unfold get_le16.
  pose proof (zslice_write_same off [y0; y1] d Ho ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [y0; y1])) with 2 in E.
  rewrite E. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma buf_write_at_comm : forall o1 l1 o2 l2 d, 0 <= o1 -> 0 <= o2 ->
  o1 + Z.of_nat (length l1) <= Z.of_nat (length d) -> o2 + Z.of_nat (length l2) <= Z.of_nat (length d) ->
  (o1 + Z.of_nat (length l1) <= o2 \/ o2 + Z.of_nat (length l2) <= o1) ->
  buf_write_at o2 l2 (buf_write_at o1 l1 d) = buf_write_at o1 l1 (buf_write_at o2 l2 d).
Proof.
  intros o1 l1 o2 l2 d H1 H2 L1 L2 D. apply zlist_ext.
  - rewrite !buf_write_at_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite !buf_write_at_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite !znth_buf_write_at by (rewrite ?buf_write_at_length; lia).
    destruct (Z.leb_spec o2 i); destruct (Z.ltb_spec i (o2 + Z.of_nat (length l2)));
    destruct (Z.leb_spec o1 i); destruct (Z.ltb_spec i (o1 + Z.of_nat (length l1))); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma swap8_split : forall off off4 d x0 x1 x2 x3 x4 x5 x6 x7, 0 <= off -> off + 8 <= Z.of_nat (length d) -> off4 = off + 4 ->
  zslice off 4 d = [x0; x1; x2; x3] -> zslice off4 4 d = [x4; x5; x6; x7] ->
  buf_write_at off4 [x3; x2; x1; x0] (buf_write_at off [x7; x6; x5; x4] d) = swap_field 8 off d.
Proof.
  intros off off4 d x0 x1 x2 x3 x4 x5 x6 x7 Ho Hl -> E0 E1.
  pose proof (get_u8_of_slice4 off d _ _ _ _ Ho ltac:(lia) E0) as (A0 & A1 & A2 & A3).
  pose proof (get_u8_of_slice4 (off + 4) d _ _ _ _ ltac:(lia) ltac:(lia) E1) as (A4 & A5 & A6 & A7). unfold get_u8 in *.
  unfold swap_field. apply zlist_ext.
  - rewrite !buf_write_at_length; cbn [length]; rewrite ?buf_write_at_length, ?length_rev, ?zslice_length; cbn [length]; lia.
  - intros i Hi. rewrite !buf_write_at_length in Hi by (cbn [length]; rewrite ?buf_write_at_length; cbn [length]; lia).
    rewrite !znth_buf_write_at by (cbn [length]; rewrite ?buf_write_at_length, ?length_rev, ?zslice_length; cbn [length]; lia).
    cbn [length]. rewrite length_rev, zslice_length by lia.
    destruct (Z.leb_spec (off + 4) i); destruct (Z.ltb_spec i (off + 4 + Z.of_nat 4));
    destruct (Z.leb_spec off i); destruct (Z.ltb_spec i (off + Z.of_nat 4)); destruct (Z.ltb_spec i (off + Z.of_nat (Z.to_nat 8)));
    cbn [andb]; try reflexivity; try lia.
    + rewrite znth_rev by (rewrite zslice_length; lia). rewrite zslice_length by lia. rewrite znth_zslice by lia.
      assert (C : i - (off + 4) = 0 \/ i - (off + 4) = 1 \/ i - (off + 4) = 2 \/ i - (off + 4) = 3) by lia.
      destruct C as [C|[C|[C|C]]]; rewrite C; cbn -[Z.add Z.sub Z.of_nat];
      [rewrite <- A3 | rewrite <- A2 | rewrite <- A1 | rewrite <- A0]; f_equal; lia.
    + rewrite znth_rev by (rewrite zslice_length; lia). rewrite zslice_length by lia. rewrite znth_zslice by lia.
      assert (C : i - off = 0 \/ i - off = 1 \/ i - off = 2 \/ i - off = 3) by lia.
      destruct C as [C|[C|[C|C]]]; rewrite C; cbn -[Z.add Z.sub Z.of_nat];
      [rewrite <- A7 | rewrite <- A6 | rewrite <- A5 | rewrite <- A4]; f_equal; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_of_lanes : forall E y0 y1 y2 y3,
  E mod 2^32 = y0 + 256 * y1 + 65536 * y2 + 16777216 * y3 ->
  0 <= y0 < 256 -> 0 <= y1 < 256 -> 0 <= y2 < 256 -> 0 <= y3 < 256 ->
  le4 (Z_to_bv 64 E) = zbytes [y0; y1; y2; y3].
Proof.
  intros E y0 y1 y2 y3 HE H0 H1 H2 H3. apply le4_of_mod32; [reflexivity|].
  cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^32 * 2^32). change (bv_modulus 8) with 256.
  rewrite Z.rem_mul_r, HE by lia. rewrite !(Z.mod_small _ 256) by lia. lia.
Qed.
Lemma le2_of_lanes : forall E y0 y1,
  E mod 2^16 = y0 + 256 * y1 -> 0 <= y0 < 256 -> 0 <= y1 < 256 ->
  le2 (Z_to_bv 64 E) = zbytes [y0; y1].
Proof.
  intros E y0 y1 HE H0 H1. apply le2_of_mod16; [reflexivity|].
  cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^16 * 2^48). change (bv_modulus 8) with 256.
  rewrite Z.rem_mul_r, HE by lia. rewrite !(Z.mod_small _ 256) by lia. lia.
Qed.

(* [comment removed for export] *)
Definition bytes_ok (L : list Z) : Prop := Forall (fun x => 0 <= x < 256) L.

Lemma le_of_bytes_range : forall L, bytes_ok L -> 0 <= le_of_bytes L < 256 ^ (Z.of_nat (length L)).
Proof.
  induction L as [|x L IH]; intros HB; cbn [le_of_bytes length].
  - lia.
  - apply Forall_cons_iff in HB as [Hx HB]. specialize (IH HB). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma le_of_bytes_app : forall L1 L2, le_of_bytes (L1 ++ L2) = le_of_bytes L1 + 256 ^ (Z.of_nat (length L1)) * le_of_bytes L2.
Proof.
  induction L1 as [|x L1 IH]; intros L2; cbn [le_of_bytes app length].
  - lia.
  - rewrite IH. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma le_of_bytes_repeat0 : forall k L, le_of_bytes (repeat 0 k ++ L) = 256 ^ (Z.of_nat k) * le_of_bytes L.
Proof.
  intros k L. rewrite le_of_bytes_app, repeat_length.
  replace (le_of_bytes (repeat 0 k)) with 0; [lia|]. induction k; cbn; lia.
Qed.

Lemma bytes_ok_firstn : forall n L, bytes_ok L -> bytes_ok (firstn n L).
Proof. intros. unfold bytes_ok. rewrite <- (firstn_skipn n L) in H. apply Forall_app in H. tauto. Qed.
Lemma bytes_ok_skipn : forall n L, bytes_ok L -> bytes_ok (skipn n L).
Proof. intros. unfold bytes_ok. rewrite <- (firstn_skipn n L) in H. apply Forall_app in H. tauto. Qed.

Lemma le_of_bytes_split : forall n L, le_of_bytes L = le_of_bytes (firstn n L) + 256 ^ (Z.of_nat (length (firstn n L))) * le_of_bytes (skipn n L).
Proof. intros n L. rewrite <- (firstn_skipn n L) at 1. apply le_of_bytes_app. Qed.

(* [comment removed for export] *)
Lemma lanes_mod : forall n L, bytes_ok L -> le_of_bytes L mod 256 ^ (Z.of_nat n) = le_of_bytes (firstn n L).
Proof.
  intros n L HB. rewrite (le_of_bytes_split n L).
  pose proof (le_of_bytes_range (firstn n L) (bytes_ok_firstn n L HB)) as R.
  destruct (Nat.le_gt_cases (length L) n).
  - rewrite firstn_all2, skipn_all2 by lia. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r.
    apply Z.mod_small. pose proof (le_of_bytes_range L HB). rewrite firstn_all2 in R by lia.
    assert (256 ^ Z.of_nat (length L) <= 256 ^ Z.of_nat n) by (apply Z.pow_le_mono_r; lia). lia.
  - rewrite length_firstn in *. rewrite Nat.min_l in * by lia.
    set (A := le_of_bytes (firstn n L)) in *. set (B := le_of_bytes (skipn n L)) in *. set (P := 256 ^ Z.of_nat n) in *.
    replace (A + P * B) with (A + B * P) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma lanes_mod64 : forall L, bytes_ok L -> le_of_bytes L mod 18446744073709551616 = le_of_bytes (firstn 8 L).
Proof. intros. change 18446744073709551616 with (256 ^ Z.of_nat 8). apply lanes_mod. assumption. Qed.
Lemma lanes_mod32 : forall L, bytes_ok L -> le_of_bytes L mod 2^32 = le_of_bytes (firstn 4 L).
Proof. intros. change (2^32) with (256 ^ Z.of_nat 4). apply lanes_mod. assumption. Qed.
Lemma lanes_mod16 : forall L, bytes_ok L -> le_of_bytes L mod 2^16 = le_of_bytes (firstn 2 L).
Proof. intros. change (2^16) with (256 ^ Z.of_nat 2). apply lanes_mod. assumption. Qed.
Lemma lanes_wrap32 : forall L, bytes_ok L -> bv_wrap 32 (le_of_bytes L) = le_of_bytes (firstn 4 L).
Proof. intros. rewrite bv_wrap32_eq. apply lanes_mod32. assumption. Qed.

(* [comment removed for export] *)
Lemma lanes_shl : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  (Z.shiftl (le_of_bytes L) n) mod 18446744073709551616 = le_of_bytes (firstn 8 (repeat 0 k ++ L)).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite <- lanes_mod64 by (unfold bytes_ok; apply Forall_app; split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia| exact HB]).
  rewrite le_of_bytes_repeat0. rewrite Z.pow_mul_r by lia. change (2^8) with 256. f_equal. lia.
Qed.
Lemma lanes_shl_nomod : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  Z.shiftl (le_of_bytes L) n = le_of_bytes (repeat 0 k ++ L).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia. rewrite le_of_bytes_repeat0. rewrite Z.pow_mul_r by lia.
  change (2^8) with 256. lia.
Qed.
Lemma lanes_shr : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  Z.shiftr (le_of_bytes L) n = le_of_bytes (skipn k L).
Proof.
  intros k L n HB ->. rewrite Z.shiftr_div_pow2 by lia. rewrite (le_of_bytes_split k L) at 1.
  pose proof (le_of_bytes_range (firstn k L) (bytes_ok_firstn k L HB)) as R.
  destruct (Nat.le_gt_cases (length L) k).
  - rewrite firstn_all2, skipn_all2 by lia. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r. apply Z.div_small.
    rewrite firstn_all2 in R by lia. rewrite Z.pow_mul_r by lia. change (2^8) with 256.
    assert (256 ^ Z.of_nat (length L) <= 256 ^ Z.of_nat k) by (apply Z.pow_le_mono_r; lia). lia.
  - rewrite length_firstn in *. rewrite Nat.min_l in * by lia. rewrite Z.pow_mul_r by lia. change (2^8) with 256.
    set (A := le_of_bytes (firstn k L)) in *. set (B := le_of_bytes (skipn k L)) in *. set (P := 256 ^ Z.of_nat k) in *.
    replace (A + P * B) with (B * P + A) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma lanes_mask : forall j L, bytes_ok L ->
  Z.land (le_of_bytes L) (255 * 2 ^ (8 * Z.of_nat j)) = le_of_bytes (repeat 0 j ++ [nth j L 0]).
Proof.
  intros j L HB. rewrite land_mask8 by (pose proof (le_of_bytes_range L HB); lia).
  rewrite le_of_bytes_repeat0. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r.
  rewrite <- Z.shiftr_div_pow2 by lia. rewrite (lanes_shr j L) by (auto; lia).
  rewrite Z.pow_mul_r by lia. change (2^8) with 256. rewrite Z.mul_comm. f_equal.
  pose proof (bytes_ok_skipn j L HB) as HS.
  destruct (skipn j L) as [|y R] eqn:E.
  - cbn. rewrite nth_overflow; [reflexivity|]. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - apply Forall_cons_iff in HS as [Hy HR]. cbn [le_of_bytes].
    replace (y + 256 * le_of_bytes R) with (y + le_of_bytes R * 256) by lia. rewrite Z.mod_add, Z.mod_small by lia.
    replace y with (nth 0 (skipn j L) 0) by (rewrite E; reflexivity). rewrite nth_skipn. f_equal. lia.
Qed.
Lemma lanes_mask1 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 65280 = le_of_bytes [0; nth 1 L 0].
Proof. intros. change 65280 with (255 * 2 ^ (8 * Z.of_nat 1)). rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask2 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 16711680 = le_of_bytes [0; 0; nth 2 L 0].
Proof. intros. change 16711680 with (255 * 2 ^ (8 * Z.of_nat 2)). rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask0 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 255 = le_of_bytes [nth 0 L 0].
Proof. intros. change 255 with (255 * 2 ^ (8 * Z.of_nat 0)) at 1. rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask3 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 4278190080 = le_of_bytes [0; 0; 0; nth 3 L 0].
Proof. intros. change 4278190080 with (255 * 2 ^ (8 * Z.of_nat 3)). rewrite lanes_mask by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint lanes_merge (L1 L2 L : list Z) : Prop :=
  match L1, L2, L with
  | [], l2, l => l = l2
  | l1, [], l => l = l1
  | a :: l1, b :: l2, c :: l => ((a = 0 /\ c = b) \/ (b = 0 /\ c = a)) /\ lanes_merge l1 l2 l
  | _ :: _, _ :: _, [] => False
  end.
Lemma lor_shift8 : forall a b c d, 0 <= a < 256 -> 0 <= c < 256 -> 0 <= b -> 0 <= d -> (a = 0 \/ c = 0) ->
  Z.lor (a + 256 * b) (c + 256 * d) = (Z.lor a c) + 256 * Z.lor b d.
Proof.
  intros a b c d Ha Hc Hb Hd Hz.
  assert (E1 : a + 256 * b = Z.lor (256 * b) a).
  { rewrite (lor_add (256 * b) a 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia]. }
  assert (E2 : c + 256 * d = Z.lor (256 * d) c).
  { rewrite (lor_add (256 * d) c 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia]. }
  rewrite E1, E2.
  transitivity (Z.lor (Z.lor (256 * b) (256 * d)) (Z.lor a c)).
  { rewrite <- !Z.lor_assoc. f_equal. rewrite (Z.lor_comm a (Z.lor (256 * d) c)). rewrite <- Z.lor_assoc. f_equal. apply Z.lor_comm. }
  assert (R : 0 <= Z.lor a c < 256).
  { destruct Hz as [-> | ->]; [rewrite Z.lor_0_l | rewrite Z.lor_0_r]; lia. }
  replace (Z.lor (256 * b) (256 * d)) with (256 * Z.lor b d).
  2:{ rewrite !(Z.mul_comm 256). change 256 with (2^8). rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_lor. reflexivity. }
  pose proof (Z.lor_nonneg b d).
  rewrite (lor_add (256 * Z.lor b d) (Z.lor a c) 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia].
Qed.
Lemma lanes_lor : forall L1 L2 L, lanes_merge L1 L2 L -> bytes_ok L1 -> bytes_ok L2 ->
  Z.lor (le_of_bytes L1) (le_of_bytes L2) = le_of_bytes L.
Proof.
  induction L1 as [|a L1 IH]; intros L2 L HM H1 H2.
  - cbn in HM. subst L. cbn [le_of_bytes]. apply Z.lor_0_l.
  - destruct L2 as [|b L2].
    + cbn in HM. subst L. apply Z.lor_0_r.
    + destruct L as [|c L]; [destruct HM|]. cbn [lanes_merge] in HM. destruct HM as [Hc HM].
      apply Forall_cons_iff in H1 as [Ha H1]. apply Forall_cons_iff in H2 as [Hb H2].
      cbn [le_of_bytes]. pose proof (le_of_bytes_range L1 H1). pose proof (le_of_bytes_range L2 H2).
      rewrite lor_shift8 by lia. rewrite (IH L2 L) by assumption. f_equal.
      destruct Hc as [[-> ->]|[-> ->]]; [apply Z.lor_0_l | apply Z.lor_0_r].
Qed.

(* [comment removed for export] *)
Definition sx_lane (x3 : Z) : Z := if x3 <? 128 then 0 else 255.
Lemma sx_lane_range : forall x, 0 <= sx_lane x < 256.
Proof. intros. unfold sx_lane. destruct (x <? 128); lia. Qed.
Lemma lanes_sx32 : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [x0; x1; x2; x3]))) =
  le_of_bytes [x0; x1; x2; x3; sx_lane x3; sx_lane x3; sx_lane x3; sx_lane x3].
Proof.
  intros. cbn [le_of_bytes]. rewrite unsigned_sx32 by lia. unfold sx_lane.
  destruct (Z.ltb_spec x3 128); destruct (Z.ltb_spec (x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * 0)))) (2^31)); lia.
Qed.
(* [comment removed for export] *)
Lemma lanes_swrap_small : forall L, bytes_ok L -> (length L <= 3)%nat ->
  (bv_swrap 32 (le_of_bytes L)) mod 18446744073709551616 = le_of_bytes L.
Proof.
  intros L HB HL. pose proof (le_of_bytes_range L HB) as R.
  assert (256 ^ Z.of_nat (length L) <= 256 ^ 3) by (apply Z.pow_le_mono_r; lia).
  rewrite swrap32_small by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma lanes_swrap4 : forall a b c e, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= e < 256 ->
  (bv_swrap 32 (le_of_bytes [a; b; c; e])) mod 18446744073709551616 =
  le_of_bytes [a; b; c; e; sx_lane e; sx_lane e; sx_lane e; sx_lane e].
Proof.
  intros. cbn [le_of_bytes]. rewrite bv_swrap32_eq. unfold sx_lane.
  destruct (Z.ltb_spec e 128); Z.div_mod_to_equations; lia.
Qed.
Lemma lanes_swrap_any : forall L, bytes_ok L -> (4 < length L)%nat ->
  bv_swrap 32 (le_of_bytes L) = bv_swrap 32 (le_of_bytes (firstn 4 L)).
Proof.
  intros L HB HL. rewrite !bv_swrap32_eq. rewrite <- (lanes_mod32 L HB). Z.div_mod_to_equations. lia.
Qed.
Lemma lanes_swrap_shl : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  bv_swrap 32 (Z.shiftl (le_of_bytes L) n) = bv_swrap 32 (le_of_bytes (firstn 4 (repeat 0 k ++ L))).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia.
  assert (HB' : bytes_ok (repeat 0 k ++ L)).
  { unfold bytes_ok. apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia| exact HB]. }
  replace (le_of_bytes L * 2 ^ (8 * Z.of_nat k)) with (le_of_bytes (repeat 0 k ++ L))
    by (rewrite le_of_bytes_repeat0, Z.pow_mul_r by lia; change (2^8) with 256; lia).
  rewrite !bv_swrap32_eq. rewrite <- (lanes_mod32 _ HB'). Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ltu_lit_sx32 : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 ->
  bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = (k <? x).
Proof.
  intros k x Hx Hk. rewrite bv_ltu_Z, unsigned_sx32, (unsigned_lit k) by lia.
  destruct (Z.ltb_spec x (2^31)); destruct (Z.ltb_spec k x); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.
Lemma ltu_lit_sx32_falseZ : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x <= k -> bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = false.
Proof. intros. rewrite ltu_lit_sx32 by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_lit_sx32_trueZ : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k < x -> bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = true.
Proof. intros. rewrite ltu_lit_sx32 by lia. apply Z.ltb_lt. lia. Qed.
(* [comment removed for export] *)
Lemma sx32_as_swrap : forall x, sx32 (Z_to_bv 64 x) = Z_to_bv 64 (bv_swrap 32 x).
Proof.
  intros x. unfold sx32. rewrite unsigned_lit_wrap. f_equal. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_swrap_swrap : forall x y, bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x mod 2^32 <? y mod 2^32).
Proof.
  intros x y. rewrite bv_ltu_Z, !unsigned_swrap32.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound y (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (y mod 2^32) (2^31)); cbv iota;
    (destruct (Z.ltb_spec (x mod 2^32) (y mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia])).
Qed.
Lemma eqb_swrap_swrap : forall x y, bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x mod 2^32 =? y mod 2^32).
Proof.
  intros x y. unfold bv_eqb. rewrite !unsigned_swrap32.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound y (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (y mod 2^32) (2^31)); cbv iota;
    (destruct (Z.eqb_spec (x mod 2^32) (y mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
Lemma eqb_swrap_small : forall x k, 0 <= k < 2^31 -> bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 =? k).
Proof.
  intros x k Hk. unfold bv_eqb. rewrite unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.eqb_spec (x mod 2^32) k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
Lemma eqb_small_swrap : forall k x, 0 <= k < 2^31 -> bv_eqb (Z_to_bv 64 k) (Z_to_bv 64 (bv_swrap 32 x)) = (k =? x mod 2^32).
Proof.
  intros k x Hk. unfold bv_eqb. rewrite unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.eqb_spec k (x mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
(* [comment removed for export] *)
Lemma ltu_swrap_small : forall x k, 0 <= k < 2^31 -> bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 <? k).
Proof. intros. apply ltu_swrap_lit. lia. Qed.
Lemma ltu_small_swrap : forall k x, 0 <= k < 2^31 -> bv_ltu (Z_to_bv 64 k) (Z_to_bv 64 (bv_swrap 32 x)) = (k <? x mod 2^32).
Proof.
  intros k x Hk. rewrite bv_ltu_Z, unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.ltb_spec k (x mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia])).
Qed.

Ltac bytes_ok_tac := unfold bytes_ok; repeat (apply Forall_cons; [fastfirst (first [assumption | apply sx_lane_range | lia]) |]); apply Forall_nil.

(* [comment removed for export] *)
Ltac lanes_merge_compute L1 L2 :=
  lazymatch L1 with
  | [] => L2
  | ?a :: ?l1 =>
    lazymatch L2 with
    | [] => L1
    | ?b :: ?l2 =>
      let r := lanes_merge_compute l1 l2 in
      lazymatch a with
      | 0 => constr:(b :: r)
      | _ => lazymatch b with 0 => constr:(a :: r) end
      end
    end
  end.
Ltac lanes_merge_tac := cbn [lanes_merge]; repeat split; try reflexivity;
  first [ left; split; reflexivity | right; split; reflexivity ].

(* [comment removed for export] *)
Ltac lanes_step :=
  match goal with
  | |- context [ (Z.shiftl (le_of_bytes ?L) ?n) mod 18446744073709551616 ] =>
      let k := eval cbv -[sx_lane] in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (firstn 8 (repeat 0 k ++ L)) in
      replace ((Z.shiftl (le_of_bytes L) n) mod 18446744073709551616) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shl k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.shiftl (le_of_bytes ?L) ?n ] =>
      let k := eval cbv in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (repeat 0 k ++ L) in
      replace (Z.shiftl (le_of_bytes L) n) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shl_nomod k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.shiftr (le_of_bytes ?L) ?n ] =>
      let k := eval cbv -[sx_lane] in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (skipn k L) in
      replace (Z.shiftr (le_of_bytes L) n) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shr k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.land (le_of_bytes ?L) 65280 ] =>
      let y := eval cbv -[sx_lane] in (nth 1 L 0) in
      replace (Z.land (le_of_bytes L) 65280) with (le_of_bytes [0; y]) by (symmetry; apply (lanes_mask1 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 16711680 ] =>
      let y := eval cbv -[sx_lane] in (nth 2 L 0) in
      replace (Z.land (le_of_bytes L) 16711680) with (le_of_bytes [0; 0; y]) by (symmetry; apply (lanes_mask2 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 4278190080 ] =>
      let y := eval cbv -[sx_lane] in (nth 3 L 0) in
      replace (Z.land (le_of_bytes L) 4278190080) with (le_of_bytes [0; 0; 0; y]) by (symmetry; apply (lanes_mask3 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 255 ] =>
      let y := eval cbv -[sx_lane] in (nth 0 L 0) in
      replace (Z.land (le_of_bytes L) 255) with (le_of_bytes [y]) by (symmetry; apply (lanes_mask0 L); bytes_ok_tac)
  | |- context [ bv_wrap 32 (le_of_bytes ?L) ] =>
      let L2 := eval cbv -[sx_lane] in (firstn 4 L) in
      replace (bv_wrap 32 (le_of_bytes L)) with (le_of_bytes L2) by (symmetry; apply (lanes_wrap32 L); bytes_ok_tac)
  | |- context [ (le_of_bytes ?L) mod 18446744073709551616 ] =>
      let L2 := eval cbv -[sx_lane] in (firstn 8 L) in
      replace ((le_of_bytes L) mod 18446744073709551616) with (le_of_bytes L2) by (symmetry; apply (lanes_mod64 L); bytes_ok_tac)
  | |- context [ (bv_swrap 32 (le_of_bytes [?a; ?b; ?e; ?f])) mod 18446744073709551616 ] =>
      rewrite (lanes_swrap4 a b e f) by (fastfirst (first [assumption | apply sx_lane_range | lia]))
  | |- context [ bv_swrap 32 (Z.shiftl (le_of_bytes ?L) ?n) ] =>
      let k := eval cbv in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (firstn 4 (repeat 0 k ++ L)) in
      replace (bv_swrap 32 (Z.shiftl (le_of_bytes L) n)) with (bv_swrap 32 (le_of_bytes L2))
        by (symmetry; apply (lanes_swrap_shl k L n); [bytes_ok_tac | reflexivity])
  | |- context [ bv_swrap 32 (le_of_bytes (?a :: ?b :: ?e :: ?f :: _ :: _)) ] =>
      lazymatch goal with |- context [ bv_swrap 32 (le_of_bytes ?L) ] =>
        let L2 := eval cbv -[sx_lane] in (firstn 4 L) in
        replace (bv_swrap 32 (le_of_bytes L)) with (bv_swrap 32 (le_of_bytes L2))
          by (symmetry; apply (lanes_swrap_any L); [bytes_ok_tac | cbn; lia]) end
  | |- context [ (bv_swrap 32 (le_of_bytes ?L)) mod 18446744073709551616 ] =>
      replace ((bv_swrap 32 (le_of_bytes L)) mod 18446744073709551616) with (le_of_bytes L)
        by (symmetry; apply (lanes_swrap_small L); [bytes_ok_tac | cbn; lia])
  | |- context [ Z.lor (le_of_bytes ?L1) (le_of_bytes ?L2) ] =>
      let L := lanes_merge_compute L1 L2 in
      replace (Z.lor (le_of_bytes L1) (le_of_bytes L2)) with (le_of_bytes L)
        by (symmetry; apply (lanes_lor L1 L2 L); [lanes_merge_tac | bytes_ok_tac | bytes_ok_tac])
  | |- context [ bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [?x0; ?x1; ?x2; ?x3]))) ] =>
      rewrite (lanes_sx32 x0 x1 x2 x3) by lia
  end.

(* [comment removed for export] *)
Ltac bswap_arith :=
  repeat lanes_step;
  first [ rewrite lanes_mod32 by bytes_ok_tac | rewrite lanes_mod16 by bytes_ok_tac | idtac ];
  cbn [firstn le_of_bytes]; lia.

(* [comment removed for export] *)
Example bswap_arith_ex1 : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = le_of_bytes [x0; x1; x2; x3] ->
  (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) (Z.land ((Z.shiftl X 8) mod 18446744073709551616) 16711680))
          (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex1s : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [x0; x1; x2; x3]))) ->
  (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
         (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex2 : forall x0 x1 x2 x3 x4 x5 x6 x7 X0 X1,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  0 <= x4 < 256 -> 0 <= x5 < 256 -> 0 <= x6 < 256 -> 0 <= x7 < 256 ->
  X0 = le_of_bytes [x0; x1; x2; x3] -> X1 = le_of_bytes [x4; x5; x6; x7] ->
  (Z.shiftr (Z.lor (Z.lor ((Z.shiftl X0 56) mod 18446744073709551616) ((Z.shiftl (Z.land X0 65280) 40) mod 18446744073709551616))
       (Z.lor ((Z.shiftl (Z.land (Z.lor ((Z.shiftl X1 32) mod 18446744073709551616) X0) 16711680) 24) mod 18446744073709551616)
             ((Z.shiftl ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.lor ((Z.shiftl X1 32) mod 18446744073709551616) X0)) 24)) mod 18446744073709551616) 32) mod 18446744073709551616))) 32) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X0 X1. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex3 : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = le_of_bytes [x0; x1; x2; x3] ->
  Z.lor (Z.lor ((bv_swrap 32 (Z.shiftl X 24)) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
        (Z.lor (Z.land (Z.shiftr X 8) 65280) (Z.shiftr X 24))
  = le_of_bytes [x3; x2; x1; x0; sx_lane x0; sx_lane x0; sx_lane x0; sx_lane x0].
Proof. intros. subst X. repeat lanes_step. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap32_mod32 : forall x, bv_swrap 32 (x mod 2^32) = bv_swrap 32 x.
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_add_mod64_l : forall x y, bv_swrap 32 ((bv_swrap 32 x) mod 18446744073709551616 + y) = bv_swrap 32 (x + y).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_add_mod64_r : forall x y, bv_swrap 32 (y + (bv_swrap 32 x) mod 18446744073709551616) = bv_swrap 32 (y + x).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma Z_to_bv64_mod : forall x, Z_to_bv 64 (x mod 18446744073709551616) = Z_to_bv 64 x.
Proof. intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. apply Z.mod_mod. lia. Qed.
Lemma unsigned_RF : forall x, bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (bv_swrap 32 x) mod 18446744073709551616.
Proof. intros. rewrite unsigned_lit_wrap. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sat_idiom : forall a b,
  Z_to_bv 64 (Z.lor ((0 - Z.b2z ((bv_swrap 32 (a + b)) mod 18446744073709551616 <? (bv_swrap 32 a) mod 18446744073709551616)) mod 18446744073709551616)
                    ((bv_swrap 32 (a + b)) mod 18446744073709551616))
  = Z_to_bv 64 (bv_swrap 32 (u_int_sum (a mod 2^32) (b mod 2^32))).
Proof.
  intros a b.
  pose proof (ltu_swrap_swrap (a + b) a) as E. rewrite bv_ltu_Z, !unsigned_RF in E. rewrite E. clear E.
  unfold u_int_sum, UINT_MAX.
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound b (2^32) ltac:(lia)).
  destruct (Z.leb_spec (b mod 2^32) (2^32 - 1 - a mod 2^32)).
  - replace ((a + b) mod 2^32 <? a mod 2^32) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
    cbn [Z.b2z Z.sub]. rewrite Z.lor_0_l. rewrite Z_to_bv64_mod. f_equal.
    rewrite !bv_swrap32_eq. Z.div_mod_to_equations; lia.
  - replace ((a + b) mod 2^32 <? a mod 2^32) with true by (symmetry; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
    cbn [Z.b2z]. change ((0 - 1) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.lor_comm, Z.lor_ones_low; [apply bv_eq; vm_compute; reflexivity | |].
    + apply Z.mod_pos_bound. lia.
    + destruct (Z.eq_dec ((bv_swrap 32 (a + b)) mod 18446744073709551616) 0) as [-> | NZ]; [cbn; lia|].
      apply Z.log2_lt_pow2; [pose proof (Z.mod_pos_bound (bv_swrap 32 (a + b)) 18446744073709551616); lia|].
      change (2 ^ 64) with 18446744073709551616. apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
Lemma u_int_sum_range : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 -> 0 <= u_int_sum a b < 2^32.
Proof. intros. unfold u_int_sum, UINT_MAX. destruct (Z.leb_spec b (2^32 - 1 - a)); lia. Qed.

(* [comment removed for export] *)
Lemma zslice_length_le : forall {A} off n (d : list A), 0 <= n -> (length (zslice off n d) <= Z.to_nat n)%nat.
Proof. intros. unfold zslice, zfirstn. rewrite length_firstn. lia. Qed.
Lemma get_le32_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_le32 d k < 2^32.
Proof.
  intros d k HF. unfold get_le32.
  pose proof (le_of_bytes_range (zslice k 4 d) (zslice_range k 4 d HF)) as R.
  pose proof (zslice_length_le k 4 d ltac:(lia)) as L.
  assert (256 ^ Z.of_nat (length (zslice k 4 d)) <= 256 ^ 4) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma get_le16_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_le16 d k < 65536.
Proof.
  intros d k HF. unfold get_le16.
  pose proof (le_of_bytes_range (zslice k 2 d) (zslice_range k 2 d HF)) as R.
  pose proof (zslice_length_le k 2 d ltac:(lia)) as L.
  assert (256 ^ Z.of_nat (length (zslice k 2 d)) <= 256 ^ 2) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma get_u8_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_u8 d k < 256.
Proof.
  intros d k HF. unfold get_u8, znth. destruct (k <? 0); [lia|].
  destruct (nth_in_or_default (Z.to_nat k) d 0) as [HI | ->]; [|lia].
  rewrite Forall_forall in HF. apply HF. exact HI.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_128 : forall x, 0 <= x < 256 -> Z.land x 128 = (if x <? 128 then 0 else 128).
Proof.
  intros x Hx. change 128 with (2^7) at 1. rewrite land_single_bit by lia.
  change (2^(7+1)) with 256. change (2^7) with 128. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma signed_negZ : forall x, -2^63 <= x < 0 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 64) with 64. change (2^64 `div` 2) with (2^63). Z.div_mod_to_equations. lia.
Qed.
Lemma lts_negZ : forall x y, -2^63 <= x < 0 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. unfold bv_lts. rewrite signed_negZ, signed_small by lia. apply Z.ltb_lt. lia. Qed.
Lemma le4_swrap : forall v, le4 (Z_to_bv 64 (bv_swrap 32 v)) = le4 (Z_to_bv 64 v).
Proof.
  intros v. unfold le4. rewrite !unsigned_lit_wrap.
  rewrite <- (Z_to_le_bytes_mod 4 ((bv_swrap 32 v) mod 2^64) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (v mod 2^64) 32) by (cbn; lia). f_equal.
  rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia.
Qed.
Lemma rw_cells_ext : forall segs m A cs cs', cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' ->
  rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' EB ES WF [[_ B] W]. split; [split; [exact WF|]|].
  - rewrite <- EB. exact B.
  - rewrite <- ES. exact W.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_3 : forall v, 0 <= v -> Z.land v 3 = v mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_65532 : forall v, 0 <= v -> Z.land v 65532 = v mod 65536 - v mod 4.
Proof.
  intros v Hv.
  assert (E : Z.land v 65532 = Z.ldiff (Z.land v (Z.ones 16)) (Z.ones 2)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, !Z.land_spec.
    change 65532 with (Z.ldiff (Z.ones 16) (Z.ones 2)). rewrite Z.ldiff_spec. rewrite Bool.andb_assoc. reflexivity. }
  rewrite E, Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^16) with 65536. change (2^2) with 4. Z.div_mod_to_equations. lia.
Qed.
Lemma shlr48 : forall v, 0 <= v -> Z.shiftr ((Z.shiftl v 48) mod 18446744073709551616) 48 = v mod 65536.
Proof. intros. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_sub_mod64_l : forall x y, bv_swrap 32 ((bv_swrap 32 x) mod 18446744073709551616 - y) = bv_swrap 32 (x - y).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Lemma swap16_val : forall x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 ->
  Z.lor ((Z.shiftl (x0 + 256 * x1) 8) mod 18446744073709551616) (Z.shiftr (x0 + 256 * x1) 8) = x1 + 256 * x0 + 65536 * x1.
Proof.
  intros x0 x1 H0 H1. replace (x0 + 256 * x1) with (le_of_bytes [x0; x1]) by (cbn; lia).
  repeat lanes_step. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma tlv_pair : forall p p2 d x0 x1 x2 x3, 0 <= p -> p + 4 <= Z.of_nat (length d) -> p2 = p + 2 ->
  zslice p 2 d = [x0; x1] -> zslice p2 2 d = [x2; x3] ->
  buf_write_at p2 [x3; x2] (buf_write_at p [x1; x0] d) = swap_field 2 p (swap_field 2 p2 d).
Proof.
  intros p p2 d x0 x1 x2 x3 Hp Hl -> E0 E1. unfold swap_field.
  rewrite E1. cbn [rev app].
  rewrite (zslice_write_other (p + 2) [x3; x2] d p 2) by (cbn [length]; lia). rewrite E0. cbn [rev app].
  apply buf_write_at_comm; cbn [length]; lia.
Qed.
Lemma tlv_pair_size : forall p p2 d x0 x1 x2 x3, 0 <= p -> p + 4 <= Z.of_nat (length d) -> p2 = p + 2 ->
  get_le16 (buf_write_at p2 [x3; x2] (buf_write_at p [x1; x0] d)) p = x1 + 256 * x0.
Proof.
  intros p p2 d x0 x1 x2 x3 Hp Hl ->. unfold get_le16.
  rewrite (zslice_write_other (p + 2) [x3; x2] _ p 2) by (cbn [length]; rewrite ?buf_write_at_length; cbn [length]; lia).
  pose proof (zslice_write_same p [x1; x0] d Hp ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [x1; x0])) with 2 in E.
  rewrite E. cbn. lia.
Qed.
End TwB.
