(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command
   (0x89968, 135 instructions), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1.v..ACh8.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed by the shadow tokens
   (PaShadow.v), and the strcmp wrapper's call stepped through by its contract (PaArt.v aj_art_at). The two loops
   are cut at their heads (0x899dc, 0x89a6c) and at the outer latch (0x89ab0); each piece is re-seeded from the
   concrete state there and the loops are proved by induction. Every call is strcmp, which writes only its stack
   window, so the memory below the frame stays the entry's (kept_out) and the read-only bytes strcmp reads
   (rt_rom_view) follow from the statement's arodata_okP. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 532 of its 679 lines of code are new or changed and 1344 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_segments_s1.v, with its module names changed; 33 of its 67 lines of code are new or changed and 645 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the byte lemmas of segment B8b's JOIN
   piece of reac_segconf_parse_file (lib/B/Prog/pf_seg_B8b_j.v): a 4-byte field of the block c read through a reader
   (the u32 encoding of SegModel's record, seg_spec.u32_enc = le4) and the 4 bytes a `sw` of a sign-extended word
   leaves. No machine state, no image, no Section hypothesis. A B8b sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: byte-encoding lemma for the B8b segment lane).
   ADAPTED from a working branch's lib/A/Prog/pf_a8a_k.v (a8_le4_byte, a8_u32_at, a8_val_mem_of_sa;
   an image-A segment lane) over image B's kit (lib/B YG0f, SegABase). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YP03 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module PMem := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.

(* byte k of the little-endian encoding of a 32-bit value is the reader's byte k of it (pf_a8a_k.v a8_le4_byte) *)
Lemma pb8bj_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (PMem.le4 (Z_to_bv 64 v)) seg_spec.ZERO) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold PMem.le4. rewrite unsigned_lit_small by lia.
unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth Z.of_nat];
rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
rewrite ?Z.shiftr_shiftr by lia; rewrite ?Z.mul_0_r, ?Z.shiftr_0_r; try reflexivity; f_equal; f_equal; lia.
Qed.
(* the u32 field at k of a struct read through a reader (pf_a8a_k.v a8_u32_at) *)
Lemma pb8bj_u32_at : forall (rd : reader) a bs k v, sa_bytes rd a bs -> 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  seg_spec.u32_enc v (seg_spec.fldz k 4 bs) -> sa_val rd (a + k) 4 v.
Proof.
intros rd a bs k v H Hk Hl (Hv & E) j Hj.
replace (a + k + Z.of_nat j) with (a + Z.of_nat (Z.to_nat k + j)) by lia.
rewrite (H (Z.to_nat k + j)%nat) by lia. f_equal.
rewrite <- (pb8bj_le4_byte v j Hv Hj). rewrite <- E. unfold seg_spec.fldz, seg_spec.fld.
change (Z.to_nat 4) with 4%nat. rewrite nth_firstn, nth_skipn.
replace (j <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
Qed.
(* a reader's value as the memory's (pf_a8a_k.v a8_val_mem_of_sa) *)
Lemma pb8bj_val_mem_of_sa : forall segs H mem a n v, sa_val (aview segs H mem) a n v ->
  val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
(* the 4 bytes a memory holds as val_mem, read through the reader, are the encoding le4 of the value *)
Lemma pb8bj_bytes_of_val_mem : forall segs H mem a v, 0 <= v < 2 ^ 32 ->
  val_mem segs (mrestrict H mem) a 4 v -> sa_bytes (aview segs H mem) a (PMem.le4 (Z_to_bv 64 v)).
Proof.
intros segs H mem a v Hv HM k Hk. rewrite PMem.length_le4 in Hk.
unfold aview. rewrite (HM k Hk). cbn [option_map]. f_equal.
change ZB0 with seg_spec.ZERO. rewrite (pb8bj_le4_byte v k Hv Hk).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* the low 32 bits of a 32-bit value sign-extended to 64 bits, as YP0e.U_SExt writes it *)
Lemma pb8bj_sext_lo : forall g, 0 <= g < 2 ^ 32 ->
  (bv_swrap 32 (g mod 2 ^ Z.of_N 32) mod 2 ^ 64) mod 2 ^ (8 * Z.of_N 4) = g.
Proof.
intros g Hg. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
rewrite (Z.mod_small g (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
change (2 ^ 32 / 2) with (2 ^ 31).
pose proof (Z.div_mod (g + 2 ^ 31) (2 ^ 32) ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (g + 2 ^ 31) (2 ^ 32) ltac:(lia)) as B1.
set (x := (g + 2 ^ 31) mod 2 ^ 32) in *. set (q1 := (g + 2 ^ 31) / 2 ^ 32) in *.
pose proof (Z.div_mod (x - 2 ^ 31) (2 ^ 64) ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (x - 2 ^ 31) (2 ^ 64) ltac:(lia)) as B2.
set (y := (x - 2 ^ 31) mod 2 ^ 64) in *. set (q2 := (x - 2 ^ 31) / 2 ^ 64) in *.
pose proof (Z.div_mod y (2 ^ 32) ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound y (2 ^ 32) ltac:(lia)) as B3.
set (w := y mod 2 ^ 32) in *. set (q3 := y / 2 ^ 32) in *.
lia.
Qed.
