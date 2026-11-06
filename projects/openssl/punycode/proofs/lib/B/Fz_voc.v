(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require StoreOk.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ImageA.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require WpEngine LibKit StrKit AShadow KBridge.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require BRt BCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Abbreviation W z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma ASEGS_asegs : BCode.BSEGS = bsegs. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma find_segment_off : forall segs lo hi,
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi)) segs = true ->
  forall a, a < lo \/ hi <= a -> find_segment segs a 1 = None.
Proof.
  induction segs as [|seg segs IH]; intros lo hi H a Ha; cbn [find_segment forallb] in *; [reflexivity|].
  apply andb_prop in H as (H1 & H2). apply andb_prop in H1 as (B1 & B2). apply Z.leb_le in B1, B2.
  destruct (Z.leb_spec (Z.of_N (seg_base seg)) a) as [L1|L1]; destruct (Z.leb_spec (a + 1) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))) as [L2|L2];
    cbn [andb]; try (exact (IH lo hi H2 a Ha)). exfalso. lia.
Qed.

Lemma asegs_hull_b : forallb (fun seg => (0x10000 <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? 0xbfd000)) bsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seg_rom_off : forall a : word, bv_unsigned a < 0x10000 \/ 0xbfd000 <= bv_unsigned a -> seg_rom bsegs a = None.
Proof.
  intros a H. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (find_segment_off bsegs 0x10000 0xbfd000 asegs_hull_b (bv_unsigned a) H). reflexivity.
Qed.
(* [comment removed for export] *)
Definition mrd_offA := KBridge.mrd_off bsegs 0x10000 0xbfd000 seg_rom_off.
Definition bytes_offA := KBridge.bytes_off bsegs 0x10000 0xbfd000 seg_rom_off.
Definition rd_ok_bytesA := KBridge.rd_ok_bytes bsegs 0x10000 0xbfd000 seg_rom_off.
Definition rd_ok_stkA := KBridge.rd_ok_stk bsegs 0x10000 0xbfd000 seg_rom_off.

(* [comment removed for export] *)
Lemma sha_shad : forall x, AShadow.sha x = shad x. Proof. reflexivity. Qed.

Lemma shad_off : forall x, 0 <= x -> 0xbfd000 <= shad x.
Proof. intros x Hx. unfold shad, SHB. pose proof (Z.div_pos x 8 Hx ltac:(lia)). lia. Qed.

Lemma addr_ok_of_acc : forall (m : word -> option byte) a n, 0 <= a -> a + n <= 2 ^ 63 -> acc bsegs m a n -> AShadow.addr_ok m a n.
Proof.
  intros m a n Ha Hn H x Hx. destruct (H (x - a) ltac:(lia)) as (b & Hb & Hok). replace (a + (x - a)) with x in * by lia.
  exists b. split.
  - pose proof (bytes_offA m (shad x) [b] 0 Hb ltac:(right; apply shad_off; lia) ltac:(cbn; lia)) as R.
    rewrite Z.add_0_r in R. exact R.
  - unfold sh_ok in Hok. destruct Hok as [Hz|(H1 & H2)]; [left; exact Hz | right; lia].
Qed.

Lemma zeros_of_bytes : forall (m : word -> option byte) a n, bytes_at bsegs m a (repeat z8 n) ->
  (a + Z.of_nat n <= 0x10000 \/ 0xbfd000 <= a) -> AShadow.zeros m a (Z.of_nat n).
Proof.
  intros m a n H HO i Hi. rewrite (bytes_offA m a _ i H); [| rewrite repeat_length; exact HO | rewrite repeat_length; exact Hi].
  rewrite nth_error_repeat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shw_ok_of_stk : forall (m : word -> option byte) lo hi a n, stk bsegs m lo hi -> 0xbfd000 <= lo ->
  lo <= AShadow.sha a / 8 * 8 -> AShadow.sha (a + n - 1) / 8 * 8 + 8 <= hi -> AShadow.shw_ok m a n.
Proof.
  intros m lo hi a n S HO H1 H2. unfold AShadow.shw_ok.
  apply (rd_ok_stkA m lo hi); [exact S | right; exact HO | exact H1 | lia].
Qed.

(* [comment removed for export] *)
Lemma strbytes_of_bytes : forall (m : word -> option byte) p bs, bytes_at bsegs m p bs ->
  (p + Z.of_nat (length bs) <= 0x10000 \/ 0xbfd000 <= p) ->
  StrKit.bytes_at m p (Z.of_nat (length bs)) (fun i => nth (Z.to_nat i) bs z8).
Proof.
  intros m p bs H HO i Hi. rewrite (bytes_offA m p bs i H HO Hi).
  apply nth_error_nth'. lia.
Qed.

(* [comment removed for export] *)
Lemma ro_addr_A : forall i, 0x10000 <= i < 0x56b000 -> ro_addr bsegs (W i) = true.
Proof.
  intros i Hi. unfold ro_addr. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  unfold bsegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
  unfold AsanUbsan.AsanUbsan_segment_000, AsanUbsan.AsanUbsan_segment_001. cbn [seg_base seg_size].
  destruct (Z_lt_dec i 0x194000) as [L|L].
  - rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  - rewrite (proj2 (Z.leb_le (Z.of_N 65536) i)) by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [andb].
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

Lemma img_ok_ro : forall (m : word -> option byte) lo hi, mem_inv bsegs m -> 0x10000 <= lo -> hi <= 0x56b000 -> LibKit.img_ok m lo hi.
Proof.
  intros m lo hi MI H1 H2 i Hi. destruct (m (W i)) as [b|] eqn:E; [| reflexivity].
  pose proof (mem_inv_ro bsegs m (W i) b MI E) as R. rewrite ro_addr_A in R by lia. discriminate R.
Qed.
