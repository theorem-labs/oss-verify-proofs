(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v; 312 of its 358 lines of code are new or changed and 587 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_bytes_A.v; 619 of its 669 lines of code are new or changed and 308 lines of the source are left out. *)
(* The image-A walk of diginet_strip_leds_encode (0x85834, 146 instructions, frame 16, a leaf) against
   lib/A/Prog/CPgEncC.v's cdc_sleds_specX, over the concrete image table of lib/A/ACef.v and the shared
   plumbing of lib/A/Prog/CPgWalk.v.

   a0 = p, a1 = strip, a2 = bits, a3 = out. The prologue saves ra at sp - 8; that is the only store
   outside out. p = 0 returns -1 (the personality is absent); else the call reads p + 16 (the device, lb)
   and p + 17 (the strip count, lbu) and writes the 32 bytes of the command at out: bits > 127 returns
   -11, strip >= the strip count returns -11, a negative device returns -1, strip > 127 returns -11, and
   the success path stores out[0..7) = f0 13 dev 20 strip bits f7, out[24] = 7, out[25] = 0 and the word
   strip | 0x50000 at out + 28, and returns 0. Every failing return comes before the first store, so out
   holds `before` there (cmd_outZ before None).

   Each personality load and each store into out is checked against the shadow byte of the address, read
   through the .got slot of the shadow-offset cell; the premises crd_ok (p + 16, 4 bytes) and cdst_ok
   (out, 32 bytes) put both ranges in the walk's shadow entries, so no check fails and the error path is
   never reached. The GOT slot and the cell are read once, at 0x8584c-0x85854; after that the walk's state
   carries the personality bytes and the 32 bytes of out instead (sl_swap), which is what lets the walk
   hold a region at p + 16 without assuming the caller's object misses the image's two cells.

   The chunk-to-garr8 lemma follows proofs/libreac/fuzz_identity/lib/A/Prog/reac_identity_fw_str.v's
   fw_garr8 / fw_le_byte1 (origin/ossv/recipes 4b6f0df50aa7); the walk's shape is CPgWalk's. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= the Gallina result on each of the walk's paths ======================= *)
Lemma sl_spec_none : forall strip bits, strip_leds_spec None strip bits = (E_ARG, None).
Proof. reflexivity. Qed.
Lemma sl_spec_bits : forall d strip bits, 127 < bits ->
strip_leds_spec (Some d) strip bits = (E_RANGE, None).
Proof.
intros d strip bits Hb. cbn [strip_leds_spec].
destruct (Z.leb_spec (d_strips d) strip) as [H|H]; [reflexivity|].
unfold leds_spec. rewrite (proj2 (Z.ltb_lt 0x7f bits)) by lia. reflexivity.
Qed.
Lemma sl_spec_strips : forall d strip bits, d_strips d <= strip ->
strip_leds_spec (Some d) strip bits = (E_RANGE, None).
Proof.
intros d strip bits H. cbn [strip_leds_spec]. rewrite (proj2 (Z.leb_le (d_strips d) strip)) by lia. reflexivity.
Qed.
Lemma sl_spec_dev : forall d strip bits, strip < d_strips d -> bits <= 127 -> 128 <= d_dev d ->
strip_leds_spec (Some d) strip bits = (E_ARG, None).
Proof.
intros d strip bits Hs Hb Hd. cbn [strip_leds_spec].
rewrite (proj2 (Z.leb_gt (d_strips d) strip)) by lia.
unfold leds_spec, sysex_spec. rewrite (proj2 (Z.ltb_ge 0x7f bits)) by lia.
rewrite (proj2 (Z.ltb_lt 0x7f (d_dev d))) by lia. reflexivity.
Qed.
Lemma sl_tb7_lo : forall x, 0 <= x < 128 -> Z.testbit x 7 = false.
Proof.
intros x H. rewrite Z.testbit_false by lia. change (2 ^ 7) with 128.
rewrite (Z.div_small x 128) by lia. reflexivity.
Qed.
Lemma sl_tb7_hi : forall x, 128 <= x < 256 -> Z.testbit x 7 = true.
Proof.
intros x H. rewrite Z.testbit_true by lia. change (2 ^ 7) with 128.
replace (x / 128) with 1 by (Z.div_mod_to_equations; lia). reflexivity.
Qed.
Lemma sl_spec_strip : forall d strip bits, strip < d_strips d -> bits <= 127 -> d_dev d <= 127 ->
127 < strip -> 0 <= strip < 256 ->
strip_leds_spec (Some d) strip bits = (E_RANGE, None).
Proof.
intros d strip bits Hs Hb Hd Hst Hr. cbn [strip_leds_spec].
rewrite (proj2 (Z.leb_gt (d_strips d) strip)) by lia.
unfold leds_spec, sysex_spec, u8. rewrite (proj2 (Z.ltb_ge 0x7f bits)) by lia.
rewrite (proj2 (Z.ltb_ge 0x7f (d_dev d))) by lia.
cbn [existsb]. rewrite (Z.mod_small strip 256) by lia.
rewrite sl_tb7_hi by lia. reflexivity.
Qed.
Lemma sl_spec_ok : forall d strip bits, strip < d_strips d -> 0 <= bits <= 127 -> 0 <= d_dev d <= 127 ->
0 <= strip <= 127 ->
strip_leds_spec (Some d) strip bits =
(0, Some ([0xf0; 0x13; d_dev d; 0x20; strip; bits; 0xf7], KEY 5 strip, 0)).
Proof.
intros d strip bits Hs Hb Hd Hst. cbn [strip_leds_spec].
rewrite (proj2 (Z.leb_gt (d_strips d) strip)) by lia.
unfold leds_spec, sysex_spec, u8. rewrite (proj2 (Z.ltb_ge 0x7f bits)) by lia.
rewrite (proj2 (Z.ltb_ge 0x7f (d_dev d))) by lia.
cbn [existsb]. rewrite (Z.mod_small strip 256), (Z.mod_small bits 256) by lia.
rewrite (sl_tb7_lo strip), (sl_tb7_lo bits) by lia.
reflexivity.
Qed.

(* ======================= the bytes the engine's stored values hold ======================= *)
(* `slli b 8 | s` of two bytes: the low byte is s, the next is b *)
Lemma sl_lor256 : forall b s, 0 <= b -> 0 <= s < 256 -> Z.lor (b * 256) s = b * 256 + s.
Proof.
intros b s Hb Hs.
assert (Hl : Z.land (b * 256) s = 0).
{ apply Z.bits_inj_0. intros k.
  destruct (Z_lt_le_dec k 8) as [Hk|Hk].
  - rewrite Z.land_spec. replace (b * 256) with (Z.shiftl b 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    rewrite Z.shiftl_spec_low by lia. reflexivity.
  - assert (Hp : 256 <= 2 ^ k) by (change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia).
    rewrite Z.land_spec. replace (Z.testbit s k) with false; [apply andb_false_r|].
    symmetry. rewrite Z.testbit_false by lia. rewrite Z.div_small by lia. reflexivity. }
rewrite Z.add_nocarry_lxor by exact Hl. symmetry. apply Z.lxor_lor. exact Hl.
Qed.

Section v. Context {fx : YK11.FPState}.
(* the byte a stored value leaves, as a Z *)
Lemma sl_byteU : forall (Ev : env) (e : sv) i, 0 <= i ->
bv_unsigned (byte_of_word (sv_denot Ev e) i) = Z.shiftr (U Ev e) (8 * i) mod 256.
Proof.
intros Ev e i Hi. unfold byte_of_word. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. reflexivity.
Qed.
Lemma sl_B_lit : forall (Ev : env) z i, 0 <= i -> 0 <= z < 2 ^ 64 ->
bv_unsigned (byte_of_word (sv_denot Ev (SLit z)) i) = Z.shiftr z (8 * i) mod 256.
Proof.
intros Ev z i Hi Hz. rewrite (sl_byteU Ev _ i Hi), U_SLit, zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma sl_B_atom : forall (Ev : env) n v i, i = 0 -> ew Ev n = Z_to_bv 64 v -> 0 <= v < 256 ->
bv_unsigned (byte_of_word (sv_denot Ev (SOff n 0)) i) = v.
Proof.
intros Ev n v i -> Hn Hv. rewrite (sl_byteU Ev _ 0 ltac:(lia)), (cw_U_atom0 Ev n v Hn ltac:(lia)).
rewrite Z.mul_0_r, Z.shiftr_0_r. apply Z.mod_small. lia.
Qed.
(* the value a sign-extending byte load leaves, as a Z: v when v < 128, v - 256 + 2 ^ 64 otherwise *)
Lemma sl_U_sx : forall (Ev : env) n v, ew Ev n = Z_to_bv 64 v -> 0 <= v < 256 ->
U Ev (SExt true 8 (SOff n 0)) = (if v <? 128 then v else v - 256 + 2 ^ 64).
Proof.
intros Ev n v Hn Hv. rewrite U_SExt. cbv beta iota.
rewrite (cw_U_atom0 Ev n v Hn ltac:(lia)). change (2 ^ Z.of_N 8) with 256.
rewrite (Z.mod_small v 256) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64). change (256 / 2) with 128.
destruct (Z.ltb_spec v 128) as [Hl|Hl].
- rewrite (Z.mod_small (v + 128) 256) by lia. replace (v + 128 - 128) with v by lia.
  apply Z.mod_small. lia.
- replace (v + 128) with ((v - 128) + 1 * 256) by lia. rewrite Z_mod_plus_full.
  rewrite (Z.mod_small (v - 128) 256) by lia. replace (v - 128 - 128) with (v - 256) by lia.
  rewrite <- (Z_mod_plus_full (v - 256) 1 (2 ^ 64)).
  rewrite (Z.mod_small (v - 256 + 1 * 2 ^ 64) (2 ^ 64)) by lia. lia.
Qed.
Lemma sl_B_sx : forall (Ev : env) n v i, i = 0 -> ew Ev n = Z_to_bv 64 v -> 0 <= v < 256 ->
bv_unsigned (byte_of_word (sv_denot Ev (SExt true 8 (SOff n 0))) i) = v.
Proof.
intros Ev n v i -> Hn Hv. rewrite (sl_byteU Ev _ 0 ltac:(lia)), (sl_U_sx Ev n v Hn Hv).
rewrite Z.mul_0_r, Z.shiftr_0_r.
destruct (Z.ltb_spec v 128) as [Hl|Hl]; [apply Z.mod_small; lia|].
replace (v - 256 + 2 ^ 64) with (v + 72057594037927935 * 256) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
(* the value `slli bits 8 | strip` the engine stores at out + 4 and out + 5 *)
Lemma sl_U_pack : forall (Ev : env) nb ns b s, ew Ev nb = Z_to_bv 64 b -> ew Ev ns = Z_to_bv 64 s ->
0 <= b < 256 -> 0 <= s < 256 ->
U Ev (SAlu ALU_OR (SAlu ALU_SLL (SOff nb 0) (SLit 8)) (SOff ns 0)) = b * 256 + s.
Proof.
intros Ev nb ns b s Hb Hs Rb Rs. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (cw_U_atom0 Ev nb b Hb ltac:(lia)), (cw_U_atom0 Ev ns s Hs ltac:(lia)), U_SLit.
change (zcanon 8) with 8. change (Z.land 8 63) with 8.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (b * 256)) by (unfold M64; lia).
rewrite sl_lor256 by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma sl_B_lo : forall (Ev : env) nb ns b s i, i = 0 -> ew Ev nb = Z_to_bv 64 b -> ew Ev ns = Z_to_bv 64 s ->
0 <= b < 256 -> 0 <= s < 256 ->
bv_unsigned (byte_of_word (sv_denot Ev (SAlu ALU_OR (SAlu ALU_SLL (SOff nb 0) (SLit 8)) (SOff ns 0))) i) = s.
Proof.
intros Ev nb ns b s i -> Hb Hs Rb Rs. rewrite (sl_byteU Ev _ 0 ltac:(lia)), (sl_U_pack Ev nb ns b s Hb Hs Rb Rs).
rewrite Z.mul_0_r, Z.shiftr_0_r. replace ((b * 256 + s) mod 256) with s by (Z.div_mod_to_equations; lia).
reflexivity.
Qed.
Lemma sl_U_hi : forall (Ev : env) nb ns b s, ew Ev nb = Z_to_bv 64 b -> ew Ev ns = Z_to_bv 64 s ->
0 <= b < 256 -> 0 <= s < 256 ->
U Ev (SAlu ALU_SRL (SAlu ALU_OR (SAlu ALU_SLL (SOff nb 0) (SLit 8)) (SOff ns 0)) (SLit 8)) = b.
Proof.
intros Ev nb ns b s Hb Hs Rb Rs.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (sl_U_pack Ev nb ns b s Hb Hs Rb Rs), U_SLit.
change (zcanon 8) with 8. change (Z.land 8 63) with 8.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
replace ((b * 256 + s) / 256) with b by (Z.div_mod_to_equations; lia).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma sl_B_hi : forall (Ev : env) nb ns b s i, i = 0 -> ew Ev nb = Z_to_bv 64 b -> ew Ev ns = Z_to_bv 64 s ->
0 <= b < 256 -> 0 <= s < 256 ->
bv_unsigned (byte_of_word (sv_denot Ev (SAlu ALU_SRL (SAlu ALU_OR (SAlu ALU_SLL (SOff nb 0) (SLit 8)) (SOff ns 0)) (SLit 8))) i) = b.
Proof.
intros Ev nb ns b s i -> Hb Hs Rb Rs.
rewrite (sl_byteU Ev _ 0 ltac:(lia)), (sl_U_hi Ev nb ns b s Hb Hs Rb Rs).
rewrite Z.mul_0_r, Z.shiftr_0_r. apply Z.mod_small. lia.
Qed.
(* the word `strip | 0x50000` the engine stores at out + 28, byte by byte *)
Lemma sl_key_add : forall s, 0 <= s < 256 -> KEY 5 s = 327680 + s.
Proof.
intros s Hs. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
rewrite (Z.mod_small s (2 ^ 16)) by lia. change (5 * 65536) with (1280 * 256).
rewrite (sl_lor256 1280 s ltac:(lia) Hs). lia.
Qed.
Lemma sl_U_key : forall (Ev : env) ns s, ew Ev ns = Z_to_bv 64 s -> 0 <= s < 256 ->
U Ev (SAlu ALU_OR (SOff ns 0) (SLit 327680)) = KEY 5 s.
Proof.
intros Ev ns s Hs Rs. rewrite U_SAlu. cbn [zalu_raw].
rewrite (cw_U_atom0 Ev ns s Hs ltac:(lia)), U_SLit. change (zcanon 327680) with (1280 * 256).
rewrite Z.lor_comm, (sl_lor256 1280 s ltac:(lia) Rs).
rewrite zcanon_id by (unfold M64; lia). rewrite (sl_key_add s Rs). lia.
Qed.
Lemma sl_B_k : forall (Ev : env) ns s i,
ew Ev ns = Z_to_bv 64 s -> 0 <= s < 256 -> 0 <= i ->
bv_unsigned (byte_of_word (sv_denot Ev (SAlu ALU_OR (SOff ns 0) (SLit 327680))) i)
= Z.shiftr (KEY 5 s) (8 * i) mod 256.
Proof.
intros Ev ns s i Hs Rs Hi. rewrite (sl_byteU Ev _ i Hi), (sl_U_key Ev ns s Hs Rs). reflexivity.
Qed.
(* the four bytes of le4Z k, as the engine's shifts give them *)
Lemma sl_le4_0 : forall k, Z.shiftr k (8 * 0) mod 256 = nth 0 (le4Z k) 0.
Proof. intros k. cbn [le4Z nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity. Qed.
Lemma sl_le4_1 : forall k, Z.shiftr k (8 * 1) mod 256 = nth 1 (le4Z k) 0.
Proof. intros k. cbn [le4Z nth]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * 1)) with 256. reflexivity. Qed.
Lemma sl_le4_2 : forall k, Z.shiftr k (8 * 2) mod 256 = nth 2 (le4Z k) 0.
Proof. intros k. cbn [le4Z nth]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * 2)) with 65536. reflexivity. Qed.
Lemma sl_le4_3 : forall k, Z.shiftr k (8 * 3) mod 256 = nth 3 (le4Z k) 0.
Proof. intros k. cbn [le4Z nth]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * 3)) with 16777216. reflexivity. Qed.
(* the four bytes of the key, at the four offsets of the 4-byte store *)
Lemma sl_B_k0 : forall (Ev : env) ns s i, i = 0 -> ew Ev ns = Z_to_bv 64 s -> 0 <= s < 256 ->
bv_unsigned (byte_of_word (sv_denot Ev (SAlu ALU_OR (SOff ns 0) (SLit 327680))) i) = nth 0 (le4Z (KEY 5 s)) 0.
Proof. intros Ev ns s i -> Hs Rs. rewrite (sl_B_k Ev ns s 0 Hs Rs ltac:(lia)). apply sl_le4_0. Qed.
Lemma sl_B_k1 : forall (Ev : env) ns s i, i = 1 -> ew Ev ns = Z_to_bv 64 s -> 0 <= s < 256 ->
bv_unsigned (byte_of_word (sv_denot Ev (SAlu ALU_OR (SOff ns 0) (SLit 327680))) i) = nth 1 (le4Z (KEY 5 s)) 0.
Proof. intros Ev ns s i -> Hs Rs. rewrite (sl_B_k Ev ns s 1 Hs Rs ltac:(lia)). apply sl_le4_1. Qed.
Lemma sl_B_k2 : forall (Ev : env) ns s i, i = 2 -> ew Ev ns = Z_to_bv 64 s -> 0 <= s < 256 ->
bv_unsigned (byte_of_word (sv_denot Ev (SAlu ALU_OR (SOff ns 0) (SLit 327680))) i) = nth 2 (le4Z (KEY 5 s)) 0.
Proof. intros Ev ns s i -> Hs Rs. rewrite (sl_B_k Ev ns s 2 Hs Rs ltac:(lia)). apply sl_le4_2. Qed.
Lemma sl_B_k3 : forall (Ev : env) ns s i, i = 3 -> ew Ev ns = Z_to_bv 64 s -> 0 <= s < 256 ->
bv_unsigned (byte_of_word (sv_denot Ev (SAlu ALU_OR (SOff ns 0) (SLit 327680))) i) = nth 3 (le4Z (KEY 5 s)) 0.
Proof. intros Ev ns s i -> Hs Rs. rewrite (sl_B_k Ev ns s 3 Hs Rs ltac:(lia)). apply sl_le4_3. Qed.

(* ======================= the branch conditions, as Z facts ======================= *)
(* a 32-bit C argument in a register: its unsigned value *)
Lemma sl_U_s32 : forall (Ev : env) n v, ew Ev n = w64 (s32 v) -> 0 <= v < 2 ^ 32 ->
U Ev (SOff n 0) = (if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32)).
Proof.
intros Ev n v Hn Hv. unfold w64, s32 in Hn. rewrite U_SOff, Hn, Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
destruct (Z.ltb_spec v (2 ^ 31)) as [Hl|Hl].
- rewrite (Z.mod_small v (2 ^ 64)) by lia. unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. lia.
- replace (v - 2 ^ 32) with ((v + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
  rewrite (Z.mod_small (v + (2 ^ 64 - 2 ^ 32)) (2 ^ 64)) by lia.
  unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.
(* `bltu c, v` of a literal c <= 127 against a 32-bit C argument v: c < v *)
Lemma sl_br_lit_lt : forall (Ev : env) n v c, ew Ev n = w64 (s32 v) -> 0 <= v < 2 ^ 32 -> 0 <= c < 2 ^ 31 ->
branch_taken BC_LTU (sv_denot Ev (SLit c)) (sv_denot Ev (SOff n 0)) = (c <? v).
Proof.
intros Ev n v c Hn Hv Hc. rewrite branch_ltu_U, U_SLit, zcanon_id by (unfold M64; lia).
rewrite (sl_U_s32 Ev n v Hn Hv). destruct (Z.ltb_spec v (2 ^ 31)) as [Hl|Hl]; [reflexivity|].
destruct (Z.ltb_spec c v) as [H1|H1]; destruct (Z.ltb_spec c (v + (2 ^ 64 - 2 ^ 32))) as [H2|H2];
first [reflexivity | lia].
Qed.
(* `bgeu v, m` of a 32-bit C argument v against a byte m: v < m is decided on the plain values *)
Lemma sl_br_ge_byte : forall (Ev : env) n m v b, ew Ev n = w64 (s32 v) -> 0 <= v < 2 ^ 32 ->
ew Ev m = Z_to_bv 64 b -> 0 <= b < 256 ->
branch_taken BC_GEU (sv_denot Ev (SOff n 0)) (sv_denot Ev (SOff m 0)) = negb (v <? b).
Proof.
intros Ev n m v b Hn Hv Hm Hb. rewrite branch_geu_U, (sl_U_s32 Ev n v Hn Hv).
rewrite (cw_U_atom0 Ev m b Hm ltac:(lia)).
destruct (Z.ltb_spec v (2 ^ 31)) as [Hl|Hl]; [reflexivity|].
destruct (Z.ltb_spec (v + (2 ^ 64 - 2 ^ 32)) b) as [H1|H1]; destruct (Z.ltb_spec v b) as [H2|H2];
first [reflexivity | lia].
Qed.
(* `bltz (lb d)` of a personality byte d: the device is negative exactly when 128 <= d *)
Lemma sl_s64_lo : forall x, 0 <= x < 2 ^ 63 -> YO0b.s64 x = x.
Proof. intros x H. unfold YO0b.s64. rewrite (proj2 (Z.ltb_lt x (2 ^ 63))) by lia. reflexivity. Qed.
Lemma sl_s64_hi : forall x, 2 ^ 63 <= x -> YO0b.s64 x = x - 2 ^ 64.
Proof. intros x H. unfold YO0b.s64. rewrite (proj2 (Z.ltb_ge x (2 ^ 63))) by lia. reflexivity. Qed.
Lemma sl_br_sx_neg : forall (Ev : env) n d, ew Ev n = Z_to_bv 64 d -> 0 <= d < 256 ->
branch_taken BC_LT (sv_denot Ev (SExt true 8 (SOff n 0))) (sv_denot Ev (SLit 0)) = (128 <=? d).
Proof.
intros Ev n d Hn Hd. rewrite YO0c.branch_lt.
change (bv_unsigned (sv_denot Ev (SExt true 8 (SOff n 0)))) with (U Ev (SExt true 8 (SOff n 0))).
change (bv_unsigned (sv_denot Ev (SLit 0))) with (U Ev (SLit 0)).
rewrite (sl_U_sx Ev n d Hn Hd), U_SLit. change (zcanon 0) with 0.
rewrite (sl_s64_lo 0) by lia.
destruct (Z.ltb_spec d 128) as [Hl|Hl].
- rewrite (sl_s64_lo d) by lia. rewrite (proj2 (Z.leb_gt 128 d)) by lia. apply Z.ltb_ge. lia.
- rewrite (sl_s64_hi (d - 256 + 2 ^ 64)) by lia. rewrite (proj2 (Z.leb_le 128 d)) by lia.
  apply Z.ltb_lt. lia.
Qed.
(* `beqz p` of the personality pointer *)
Lemma sl_br_eq0 : forall (Ev : env) n v, ew Ev n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot Ev (SOff n 0)) (sv_denot Ev (SLit 0)) = (v =? 0).
Proof.
intros Ev n v Hn Hv. rewrite branch_eq_U, (cw_U_atom0 Ev n v Hn Hv), U_SLit.
rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
End v.

(* ======================= garr8 from a state's chunks ======================= *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sl_le_byte1 : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
intros b. pose proof (bv_unsigned_in_range 8 b) as Hr.
change (bv_modulus 8) with 256 in Hr.
assert (E : YO0f.le_byte (bv_unsigned b) 1 0 = bv_unsigned b).
{ unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite (Z.mod_small (bv_unsigned b) 256) by lia. apply Z.mod_small. lia. }
rewrite E. apply Z_to_bv_bv_unsigned.
Qed.
(* the bytes the chunks of a region say are at its base *)
Lemma sl_garr8 : forall E m (cs : list YP09.chunk) base (l : list Z),
Forall (YP09.chunk_ok tfibsegs E m base) cs ->
(forall j, (j < length l)%nat -> exists off (n : N) e,
   off <= Z.of_nat j < off + Z.of_N n /\ In (YP09.mkChunk off (CVal n e)) cs /\
   bv_unsigned (byte_of_word (sv_denot E e) (Z.of_nat j - off)) = nth j l 0) ->
garr8 tfibsegs m base l.
Proof.
intros E m cs base l Hcs Hl j Hj. destruct (Hl j Hj) as (off & n & e & Hr & Hin & He).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
destruct (Hc (Z.of_nat j - off) ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2. injection Hb1 as Hb1. subst b.
pose proof (bv_unsigned_in_range 8 (byte_of_word (sv_denot E e) (Z.of_nat j - off))) as Hrg.
change (bv_modulus 8) with 256 in Hrg.
replace (base + off + (Z.of_nat j - off)) with (base + Z.of_nat j) in Hb2 by lia.
rewrite <- He. split; [|lia].
intros kk Hk. assert (kk = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
rewrite Hb2. f_equal. symmetry. apply sl_le_byte1.
Qed.
(* a garr8 carries to a state whose view agrees on the range *)
Lemma sl_garr8_kept : forall (W : world tfibsegs) memc (W2 : world tfibsegs) mem2 base (l : list Z),
garr8 tfibsegs (mrestrict (w_H W) memc) base l ->
(forall a, base <= a < base + Z.of_nat (length l) ->
   aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) memc a) ->
garr8 tfibsegs (mrestrict (w_H W2) mem2) base l.
Proof.
intros W memc W2 mem2 base l HG HK j Hj. destruct (HG j Hj) as (HV & HR). split; [|exact HR].
intros kk Hk. assert (kk = 0%nat) as -> by lia.
rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W2) memc mem2 (base + Z.of_nat j + Z.of_nat 0)).
- exact (HV 0%nat ltac:(lia)).
- apply HK. change (Z.of_nat 0) with 0. lia.
Qed.
(* every byte of a garr8's list is a byte *)
Lemma sl_garr8_range : forall m base (l : list Z), garr8 tfibsegs m base l -> Forall (fun x => 0 <= x < 256) l.
Proof.
intros m base l HG. apply Forall_nth. intros i dft Hi.
rewrite (nth_indep l dft 0) by exact Hi. exact (proj2 (HG i Hi)).
Qed.
End g.

(* ======================= the walk's state ======================= *)
(* the personality's device and strip count, at p + 16 and p + 17 (atoms 33, 34) *)
Definition sl_pers : YP09.region :=
YP09.mkRegion (Some 10%nat) 16 18 0 0
[YP09.mkChunk 16 (CVal 1 (SOff 33 0)); YP09.mkChunk 17 (CVal 1 (SOff 34 0))].
(* the caller's command: the 32 bytes at out, byte j in atom 35 + j *)
Definition sl_out : YP09.region :=
YP09.mkRegion (Some 13%nat) 0 32 0 32
(map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (35 + j) 0))) (seq 0 32)).
(* the shadow of the four personality bytes and of the 32 bytes of out *)
Definition sl_SH : list shent := [mkSHE 10 16 20; mkSHE 13 0 32].
(* p and out are not 0 (the two early returns are decided), each personality field is a byte *)
Definition sl_AF : list (nat * afact) :=
[(10%nat, mkAF 1 (2 ^ 47 - 21) 0); (13%nat, mkAF 1 (2 ^ 47 - 33) 0);
 (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0)].
(* what the walk may change: its save slot and the 32 bytes of out *)
Definition sl_zone (sp out : Z) (a : Z) : Prop := (sp - 16 <= a < sp) \/ (out <= a < out + 32).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the chunks of sl_out hold the bytes the caller's object holds *)
Lemma sl_out_chunks : forall E m out (l : list Z) (k n : nat),
length l = n -> garr8 tfibsegs m out l ->
(forall j, (j < n)%nat -> ew E (k + j) = Z_to_bv 64 (nth j l 0)) ->
Forall (YP09.chunk_ok tfibsegs E m out)
  (map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (k + j) 0))) (seq 0 n)).
Proof.
intros E m out l k n Hlen HG HE. apply Forall_forall. intros c Hc.
apply in_map_iff in Hc. destruct Hc as (j & <- & Hj). apply in_seq in Hj.
apply (chunk_ok_val tfibsegs E m out (Z.of_nat j) 1 (SOff (k + j) 0) (nth j l 0)).
- cbn [sv_denot]. rewrite (HE j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- change (2 ^ (8 * Z.of_N 1)) with 256. exact (proj2 (HG j ltac:(lia))).
- cbn. lia.
- exact (proj1 (HG j ltac:(lia))).
Qed.
End c.

(* ======================= the walk's tactics ======================= *)
(* an atom's value in the env of a stop: strip the run's fresh atoms, then the walk's own equation *)
Ltac sl_ew0 := rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; eassumption.
Ltac sl_ew EX :=
  rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia;
  first [ eassumption
        | lazymatch goal with |- ew _ ?n = _ =>
            let j := eval compute in (n - 35)%nat in apply (EX j); lia end ].
(* the zone of a state's write windows: the save slot (atom 2) and the 32 bytes of out (atom 13) *)
Ltac sl_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia; unfold sl_zone;
  first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = _ |- _ => rewrite B2 in Hb end; left; lia
        | lazymatch goal with B13 : bv_unsigned (ew _ 13) = _ |- _ => rewrite B13 in Hb end; right; lia
        | exfalso; lia ]
| ]); destruct Hr.
(* the write right of each window: the save slot lies in the caller's stack allowance, the bytes of out
   are the caller's to write (cdst_ok's twr_ok), every other region is read-only *)
Ltac sl_awr :=
idtac; lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0 fp b0 bc ly own);
let B2v := fresh "B2v" in let B13v := fresh "B13v" in
eassert (B2v : bv_unsigned (ew Ev 2) = _) by sl_ew0;
eassert (B13v : bv_unsigned (ew Ev 13) = _) by sl_ew0;
lazymatch type of B2v with _ = ?spv =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
  [reflexivity | rewrite B2v; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
| ((eapply cw_awr_ok_cons_twr;
   [reflexivity | exact B13v | cbn [YP09.r_wlo YP09.r_whi]; lia | idtac | eassumption | idtac ]);
  [cbn [YP09.r_wlo YP09.r_whi]; lia | idtac]) ]
end end.
(* the region of out in the state at a stop, and its chunks *)
Ltac sl_find13 l :=
lazymatch l with
| cons (YP09.mkRegion (Some 13%nat) ?lo ?hi ?wlo ?whi ?cs) _ =>
    constr:(YP09.mkRegion (Some 13%nat) lo hi wlo whi cs)
| cons _ ?t => sl_find13 t
end.
Ltac sl_chunks HCH outv :=
lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
  let l := eval vm_compute in (ss_mem ssv) in
  let r := sl_find13 l in
  let HF := fresh "HF" in let HR := fresh "HR" in let B13f := fresh "B13f" in
  pose proof (proj1 (proj2 (st_ok_mem_ok tfibsegs Ev ssv msv HS))) as HF;
  assert (HR : region_ok tfibsegs Ev (ms_mem msv) r)
    by (apply (proj1 (Forall_forall _ _) HF); change (ss_mem ssv) with l; cbn [In];
        repeat (first [left; reflexivity | right]));
  clear HF; destruct HR as (_ & _ & _ & HCH);
  cbn [YP09.r_base YP09.r_chunks base_val] in HCH;
  assert (B13f : bv_unsigned (ew Ev 13) = outv)
    by (rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; assumption);
  rewrite B13f in HCH; clear B13f
end.
(* the byte a chunk's value leaves, against the byte the result asks for *)
Ltac sl_side EX := first [reflexivity | sl_ew EX | cbn [nth]; lia].
Ltac sl_byte EX :=
  first
  [ erewrite sl_B_lit by (sl_side EX)
  | erewrite sl_B_atom by (sl_side EX)
  | erewrite sl_B_sx by (sl_side EX)
  | erewrite sl_B_lo by (sl_side EX)
  | erewrite sl_B_hi by (sl_side EX)
  | erewrite sl_B_k0 by (sl_side EX)
  | erewrite sl_B_k1 by (sl_side EX)
  | erewrite sl_B_k2 by (sl_side EX)
  | erewrite sl_B_k3 by (sl_side EX) ];
  first [ reflexivity
        | vm_compute; reflexivity
        | unfold u8; rewrite Z.mod_small by (cbn [nth]; lia); reflexivity ].
(* the 32 bytes of the caller's object, one variable each *)
Ltac sl_destruct32 l H :=
  do 32 (let x := fresh "b" in destruct l as [|x l]; [cbn in H; lia|]);
  destruct l; [|cbn in H; lia].
(* byte j of the result, from the chunk of the state that holds it *)
Ltac sl_pick EX :=
  lazymatch goal with |- exists _ _ _, _ /\ In _ ?cs /\ _ =>
    let rec go l :=
      lazymatch l with
      | cons (YP09.mkChunk ?off (CVal ?n ?e)) ?t =>
          first [ exists off, n, e; split;
                  [ cbn [Z.of_nat Z.of_N]; lia
                  | split; [cbn [In]; repeat (first [left; reflexivity | right]) | sl_byte EX] ]
                | go t ]
      | _ => fail "sl_pick: no chunk holds this byte"
      end
    in go cs
  end.
(* the 32 bytes of the result, each from the chunk of the state that holds it *)
Ltac sl_res_bytes EX HCH :=
  apply (sl_garr8 _ _ _ _ _ HCH);
  intros j Hj; cbn [cmd_outZ map app firstn skipn length le4Z] in Hj;
  do 32 (destruct j as [|j];
    [cbn [cmd_outZ map app firstn skipn length nth]; sl_pick EX|]); lia.

(* ======================= the walk ======================= *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Theorem diginet_strip_leds_encode_A_holds : cdc_sleds_specX tfibsegs B MT 0x85834.
Proof using MTL TL LAWS ML.
unfold cdc_sleds_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p strip bits out before
  HE H10 Hpers Hstrip Hbits H13 HOUT Hdisj.
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
unfold T_sleds in *.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16 HE ltac:(lia))
  as (Hceil & H47 & H46 & _ & Hpres).
pose proof HOUT as (Hcdst & Hbef & Hlen).
pose proof Hcdst as (Hout0 & Hout63 & Htdst & Htwr & Hora & Hohull & Hoam & Howin).
assert (Ho47 : out + 32 <= 2 ^ 47 - 1)
  by (unfold amem_range in Hoam; rewrite C4, C5 in Hoam; destruct Hoam as [Hl | [_ Hh]]; lia).
change (w64 out) with (Z_to_bv 64 out) in H13.
change (w64 p) with (Z_to_bv 64 p) in H10.
destruct Hstrip as (Rstrip & Estrip). destruct Hbits as (Rbits & Ebits).
(* the bytes of out are a byte each, and none of them is a byte of the image *)
pose proof (sl_garr8_range _ out before Hbef) as HBR.
assert (HEIMG : forall a, cenc_wr out a -> in_img tfibsegs a -> False).
{ intros a Ha Him. unfold cenc_wr in Ha.
  exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 a (proj1 HJ0) Htdst Ha Him). }
destruct pd as [d|].
- (* ======================= the personality is present ======================= *)
  pose proof Hpers as (Hp0 & Hp63 & Rdev & Rstrips & Rchars & Rcounter & Hpg & Hcimg).
  pose proof Hcimg as (Hq0 & Hn0 & Hq63 & Hpam & Hpwin & Himgb & Husable).
  assert (Hp47 : p + 20 <= 2 ^ 47 - 1)
    by (unfold amem_range in Hpam; rewrite C4, C5 in Hpam; destruct Hpam as [Hl | [_ Hh]]; lia).
  destruct (Husable lyc Sc W memc mdc (proj1 HJ0)) as (Hpra & Hphull).
  cbn [cpers_disj] in Hdisj.
  set (xs := d_dev d :: d_strips d :: before).
  assert (X33 : ew (Ereg regs (cw_extra xs)) 33 = Z_to_bv 64 (d_dev d)) by exact (cw_ew_x regs xs 0).
  assert (X34 : ew (Ereg regs (cw_extra xs)) 34 = Z_to_bv 64 (d_strips d)) by exact (cw_ew_x regs xs 1).
  assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) sl_AF).
  { unfold sl_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), (ew_Ereg_nat regs _ 13 13%bv eq_refl), H10, H13, X33, X34.
    rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
  pose proof (cw_entry_base_af B TL LAWS 0x85834 16 xs sl_AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16
    HE ltac:(lia) ltac:(vm_compute; reflexivity) HAF) as HS.
  remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
  assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = w64 (s32 strip)) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Estrip).
  assert (E12 : ew E 12 = w64 (s32 bits)) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact Ebits).
  assert (E13 : ew E 13 = Z_to_bv 64 out) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (B13 : bv_unsigned (ew E 13) = out) by (rewrite E13; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  assert (E33 : ew E 33 = Z_to_bv 64 (d_dev d)) by (subst E; exact X33).
  assert (E34 : ew E 34 = Z_to_bv 64 (d_strips d)) by (subst E; exact X34).
  assert (EX : forall j, (j < 32)%nat -> ew E (35 + j) = Z_to_bv 64 (nth j before 0))
    by (subst E; intros j Hj; exact (cw_ew_x regs xs (2 + j))).
  clear HEE. clearbody xs.
  assert (SHOK : sh_ok tfibsegs CW_Bx sl_SH E (mrestrict (w_H W) memc)).
  { unfold sl_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - exact (cw_shent_ra_off W memc E 10 p 16 4 Hpra Hpam ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E10 E32).
    - exact (cw_shent_cdst B STK sp0 FP ly S lyc Sc own W memc (spZ regs) 16 E 13 out 32 Hcdst E13 E32 ltac:(lia)). }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  unfold cfg_at. change (w64 0x85834) with (Z_to_bv 64 0x85834).
  (* 0x85834-0x85854: the save of ra, then the shadow offset through the .got slot and its cell *)
  cw_run_to cw_awr_stk 0x85858.
  lazymatch goal with HG : mem_grows (mrestrict _ _) (mrestrict _ ?mm) |- _ =>
    assert (HPR : forall a, apresent (w_H W) memc a -> apresent (w_H W) mm a)
      by (intros a Ha; exact (apresent_grows (w_H W) memc mm a HG Ha)) end.
  cw_keep cw_kwr_stk.
  (* the personality bytes and the bytes of out are off the save slot, so they are what they were *)
  assert (HPG : garr8 tfibsegs (mrestrict (w_H W) (ms_mem ms)) (p + 16)
    [d_dev d; d_strips d; d_chars d; d_counter d]).
  { apply (sl_garr8_kept W memc W (ms_mem ms) (p + 16) _ Hpg).
    intros a Ha. cbn [length] in Ha. apply KE; [lia | cbv beta; unfold coff_win in Hpwin; lia]. }
  assert (HOG : garr8 tfibsegs (mrestrict (w_H W) (ms_mem ms)) out before).
  { apply (sl_garr8_kept W memc W (ms_mem ms) out before Hbef).
    intros a Ha. rewrite Hlen in Ha. apply KE; [lia | cbv beta; unfold coff_win in Howin; lia]. }
  (* the shadow offset is held in a register now: drop the .got slot and the cell (the personality may
     lie on either of them), and add the personality's two bytes and the 32 bytes of out *)
  assert (Hpok : region_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) sl_pers).
  { unfold region_ok, sl_pers.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (chunk_ok_val tfibsegs E _ p 16 1 (SOff 33 0) (d_dev d));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      pose proof (proj1 (HPG 0%nat ltac:(cbn; lia))) as HV0.
      cbn [nth Z.of_nat] in HV0. rewrite Z.add_0_r in HV0. exact HV0.
    - apply (chunk_ok_val tfibsegs E _ p 17 1 (SOff 34 0) (d_strips d));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      pose proof (proj1 (HPG 1%nat ltac:(cbn; lia))) as HV1.
      cbn [nth] in HV1. change (Z.of_nat 1) with 1 in HV1.
      replace (p + 16 + 1) with (p + 17) in HV1 by lia. exact HV1. }
  assert (Hook : region_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) sl_out).
  { unfold region_ok, sl_out.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E13, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable tfibsegs); apply HPR;
            exact (proj1 (proj2 (Htwr (out + o) ltac:(lia))))|].
    exact (sl_out_chunks E _ out before 35 32%nat Hlen HOG EX). }
  cw_drop_gb.
  lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
    let HD := fresh "HD" in let HS2 := fresh "HS" in
    assert (HD : all_disjoint Ev sl_out (ss_mem ssv));
    [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, sl_out;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E13, B2, unsigned_lit_small by lia;
      unfold coff_win in Howin; split; [lia | exact I]
    | ];
    pose proof (ast_ok_add_region tfibsegs Ev ssv msv sl_out HS eq_refl Hook HD) as HS2;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HS HD; rename HS2 into HS end.
  lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
    let HD := fresh "HD" in let HS2 := fresh "HS" in
    assert (HD : all_disjoint Ev sl_pers (ss_mem ssv));
    [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, sl_pers, sl_out;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E10, E13, B2, !unsigned_lit_small by lia;
      unfold coff_win in Hpwin; split; [lia|]; split; [lia | exact I]
    | ];
    pose proof (ast_ok_add_region tfibsegs Ev ssv msv sl_pers HS eq_refl Hpok HD) as HS2;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HS HD; rename HS2 into HS end.
  (* from here the walk may also write the 32 bytes of out *)
  assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ sl_zone (spZ regs) out a ->
    aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) memc a).
  { intros a Ha Hz. apply KE; [lia | intros Hc; apply Hz; unfold sl_zone; left; exact Hc]. }
  clear KE. rename KE2 into KE.
  assert (HCOV : forall a, sl_zone (spZ regs) out a -> (spZ regs - 16 <= a < spZ regs) \/ cenc_wr out a).
  { intros a [Hz|Hz]; [left; lia | right; unfold cenc_wr; lia]. }
  (* 0x85858-0x8586c: the shadow byte of p + 17; stop at 0x85870 `bltu 127, bits` *)
  cw_run sl_awr. cw_keep sl_kwr.
  cw_branch Hb1.
  all: lazymatch type of Hb1 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
       rewrite (sl_br_lit_lt Ev 12 bits 127 ltac:(sl_ew EX) ltac:(lia) ltac:(lia)) in Hb1 end.
  + (* bits > 127: a0 = -11 *)
    apply Z.ltb_lt in Hb1.
    cw_run sl_awr. cw_keep sl_kwr.
    cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact HEIMG) ltac:(exact HCOV))
            ltac:(idtac; rewrite (sl_spec_bits d strip bits ltac:(lia)); unfold cenc_res; cbn [fst snd]; split;
                  [rewrite R10; unfold w64, E_RANGE; apply bv_eq; vm_compute; reflexivity
                  | sl_chunks HCH out; sl_destruct32 before Hlen;
                    repeat (apply Forall_cons_iff in HBR; destruct HBR as [? HBR]);
                    sl_res_bytes EX HCH]).
  + (* bits <= 127: stop at 0x85878 `bgeu strip, strips` *)
    apply Z.ltb_ge in Hb1.
    cw_run sl_awr. cw_keep sl_kwr.
    cw_branch Hb2.
    all: lazymatch type of Hb2 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
         rewrite (sl_br_ge_byte Ev 11 34 strip (d_strips d) ltac:(sl_ew EX) ltac:(lia) ltac:(sl_ew EX) ltac:(lia)) in Hb2 end.
    * (* strip >= the strip count: a0 = -11 *)
      apply negb_true_iff, Z.ltb_ge in Hb2.
      cw_run sl_awr. cw_keep sl_kwr.
      cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact HEIMG) ltac:(exact HCOV))
              ltac:(idtac; rewrite (sl_spec_strips d strip bits ltac:(lia)); unfold cenc_res; cbn [fst snd]; split;
                    [rewrite R10; unfold w64, E_RANGE; apply bv_eq; vm_compute; reflexivity
                    | sl_chunks HCH out; sl_destruct32 before Hlen;
                      repeat (apply Forall_cons_iff in HBR; destruct HBR as [? HBR]);
                      sl_res_bytes EX HCH]).
    * (* strip < the strip count: the shadow byte of p + 16, stop at 0x85894 `bltz dev` *)
      apply negb_false_iff, Z.ltb_lt in Hb2.
      cw_run sl_awr. cw_keep sl_kwr.
      cw_branch Hb3.
      all: lazymatch type of Hb3 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
           rewrite (sl_br_sx_neg Ev 33 (d_dev d) ltac:(sl_ew EX) ltac:(lia)) in Hb3 end.
      -- (* the device byte is negative: a0 = -1 *)
         apply Z.leb_le in Hb3.
         cw_run sl_awr. cw_keep sl_kwr.
         cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact HEIMG) ltac:(exact HCOV))
                 ltac:(idtac; rewrite (sl_spec_dev d strip bits ltac:(lia) ltac:(lia) ltac:(lia));
                       unfold cenc_res; cbn [fst snd]; split;
                       [rewrite R10; unfold w64, E_ARG; apply bv_eq; vm_compute; reflexivity
                       | sl_chunks HCH out; sl_destruct32 before Hlen;
                         repeat (apply Forall_cons_iff in HBR; destruct HBR as [? HBR]);
                         sl_res_bytes EX HCH]).
      -- (* the device byte is a 7-bit value: stop at 0x858a0 `bltu 127, strip` *)
         apply Z.leb_gt in Hb3.
         cw_run sl_awr. cw_keep sl_kwr.
         cw_branch Hb4.
         all: lazymatch type of Hb4 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
              rewrite (sl_br_lit_lt Ev 11 strip 127 ltac:(sl_ew EX) ltac:(lia) ltac:(lia)) in Hb4 end.
         ++ (* strip > 127: a0 = -11 *)
            apply Z.ltb_lt in Hb4.
            cw_run sl_awr. cw_keep sl_kwr.
            cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact HEIMG) ltac:(exact HCOV))
                    ltac:(idtac; rewrite (sl_spec_strip d strip bits ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
                          unfold cenc_res; cbn [fst snd]; split;
                          [rewrite R10; unfold w64, E_RANGE; apply bv_eq; vm_compute; reflexivity
                          | sl_chunks HCH out; sl_destruct32 before Hlen;
                            repeat (apply Forall_cons_iff in HBR; destruct HBR as [? HBR]);
                            sl_res_bytes EX HCH]).
         ++ (* the success path: the eight stores into out, then a0 = 0 *)
            apply Z.ltb_ge in Hb4.
            assert (E11s : ew E 11 = Z_to_bv 64 strip)
              by (rewrite E11; unfold w64, s32; rewrite (proj2 (Z.ltb_lt strip (2 ^ 31))) by lia; reflexivity).
            assert (E12s : ew E 12 = Z_to_bv 64 bits)
              by (rewrite E12; unfold w64, s32; rewrite (proj2 (Z.ltb_lt bits (2 ^ 31))) by lia; reflexivity).
            clear E11 E12.
            cw_run sl_awr. cw_keep sl_kwr.
            cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact HEIMG) ltac:(exact HCOV))
                    ltac:(idtac; rewrite (sl_spec_ok d strip bits ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
                          unfold cenc_res; cbn [fst snd]; split;
                          [rewrite R10; unfold w64; apply bv_eq; vm_compute; reflexivity
                          | sl_chunks HCH out; sl_destruct32 before Hlen;
                            repeat (apply Forall_cons_iff in HBR; destruct HBR as [? HBR]);
                            sl_res_bytes EX HCH]).
- (* ======================= the personality is NULL ======================= *)
  cbn [pers_argA] in Hpers. subst p.
  pose proof (cw_entry_base B TL LAWS 0x85834 16 (@nil Z) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 16
    HE ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
  remember (Ereg regs (cw_extra [])) as E eqn:HEE.
  assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  clear HEE.
  assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by (apply Forall_nil).
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  unfold cfg_at. change (w64 0x85834) with (Z_to_bv 64 0x85834).
  (* 0x85834-0x85840: the save of ra and a0 = -1; stop at 0x85844 `beqz p` *)
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  cw_branch Hb0.
  all: lazymatch type of Hb0 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
       rewrite (sl_br_eq0 Ev 10 0 ltac:(sl_ew0) ltac:(lia)) in Hb0 end.
  + (* taken (p = 0): the return with a0 = -1 and out untouched *)
    cw_run cw_awr_stk. cw_keep cw_kwr_stk.
    cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact HEIMG) ltac:(idtac; intros a Hz; left; cbv beta in Hz; lia))
            ltac:(idtac; cbn [strip_leds_spec]; unfold cenc_res; cbn [fst snd cmd_outZ]; split;
                  [rewrite R10; unfold w64, E_ARG; apply bv_eq; vm_compute; reflexivity
                  | apply (sl_garr8_kept W memc W _ out before Hbef);
                    intros a Ha; rewrite Hlen in Ha; apply KE;
                    [lia | cbv beta; unfold coff_win in Howin; lia]]).
  + (* not taken: p <> 0, which the premise refutes *)
    exfalso. cbn in Hb0. discriminate Hb0.
Qed.
End d.
End b.
