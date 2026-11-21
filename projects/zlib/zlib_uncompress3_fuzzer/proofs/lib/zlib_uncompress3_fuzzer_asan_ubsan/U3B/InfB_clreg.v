(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AKit U2AArr InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7h InfAGlue_w7 InfAGlue_w7b UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import InfBTables InfB_w7tab InfB_w7tab16.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import IfBTac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation amem := (word -> option byte).

Lemma shl48_shr56 : forall c, 0 <= c < 4294967296 -> Z.shiftr (Z.shiftl c 48 mod 18446744073709551616) 56 = code_bits c.
Proof.
  intros c Hc. rewrite <- code_word_bits. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change (2 ^ 48) with 281474976710656. change (2 ^ 56) with 72057594037927936. change (2 ^ 8) with 256.
  Z.div_mod_to_equations. lia.
Qed.
Lemma negw_neg : forall B, 0 <= B < 2147483648 -> bv_swrap 32 (0 - (- B) mod 18446744073709551616) = B.
Proof.
  intros B HB. destruct (Z.eq_dec B 0) as [->|NZ]; [reflexivity|].
  replace ((- B) mod 18446744073709551616) with (18446744073709551616 - B) by (apply (Z.mod_unique (- B) 18446744073709551616 (-1) (18446744073709551616 - B)); lia).
  rewrite <- (swrap32_shift (0 - (18446744073709551616 - B)) 4294967296).
  replace (0 - (18446744073709551616 - B) + 4294967296 * 4294967296) with B by lia. apply swrap32_small. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (RNG : footprint) (POST : machine_state -> Prop).

  Lemma cl_hidx : forall (x1 x2 x3 x4 x6 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA lb H : Z),
    0 <= H < 18446744073709551616 -> 1 <= lb <= 15 -> 0 < TA < 140737488355328 ->
    (forall (x11' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 TA) x6 (Z_to_bv 64 (2 ^ lb - 1)) x8 x9 x10 x11' (Z_to_bv 64 lb) (Z_to_bv 64 (H mod 2 ^ lb)) x14 x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 1) (Z_to_bv 64 H) x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f9c8) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 TA) x6 (Z_to_bv 64 (2 ^ lb - 1)) x8 x9 x10 x11 (Z_to_bv 64 lb) x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 (Z_to_bv 64 H) x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f994) fc None m (seg_rom bsegs)).
  Proof.
    intros until H. intros HH LB TAR K.
    pose proof (pow2_le_15 lb ltac:(lia)) as P15. pose proof (mod_pow2_bound H lb ltac:(lia)) as MR.
    zrunu [0x8f9a4]. rewrite (land_mask_mod' H lb) by lia.
    zs. rewrite shl2.
    zrunu [0x8f9c8].
    apply K.
  Qed.

  Lemma cl_hregs : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (B av NX : Z),
    0 <= B <= 40 -> 0 <= av < 67108864 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 (Z.shiftl av 32)) x7 x8 x9 x10 (Z_to_bv 64 NX) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 av) x19 x25 x26 x24 x20 (Z_to_bv 64 (- B)) x21 x27 (Z_to_bv 64 NX) (Z_to_bv 64 B) (Z_to_bv 64 av) (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8f9e4) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 av) x19 x25 x26 x24 x20 x23 x21 x27 (Z_to_bv 64 NX) (Z_to_bv 64 B) x30 x31) FR (Z_to_bv 64 0x8f9cc) fc None m (seg_rom bsegs)).
  Proof.
    intros until NX. intros HB HA K.
    zs. zs. zs. zs. zs. zs.
    rewrite !(Z.mod_small _ 4294967296) by lia. replace (0 - B) with (- B) by lia.
    exact K.
  Qed.

  Lemma cl_pull_g : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A B : Z),
    1 <= A < 140737488355328 -> 0 <= B <= 40 ->
    (forall (x10' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10' (Z_to_bv 64 A) x12 x13 (Z_to_bv 64 (A + 1)) x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fa58) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fa3c) fc None m (seg_rom bsegs)).
  Proof.
    intros until B. intros HA HB K.
    zrunu [0x8fa58].
    apply K.
  Qed.

  Lemma cl_join : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (c : Z),
    0 <= c < 4294967296 ->
    (forall (x10' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10' x11 x12 (Z_to_bv 64 c) (Z_to_bv 64 (code_bits c)) x15 x16 x17 x18 x22 (Z_to_bv 64 (Z.shiftr c 8)) x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fa30) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (code_val c)) x11 x12 (Z_to_bv 64 (Z.land c 65535)) x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fa20) fc None m (seg_rom bsegs)).
  Proof.
    intros until c. intros CR K.
    pose proof (code_val_range c) as VALR.
    assert (LO : 0 <= Z.land c 65535 < 65536) by (change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    assert (SH : 0 <= Z.shiftl (code_val c) 16 < 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 16) with 65536; lia).
    zs. zs. rewrite ?(Z.mod_small (Z.shiftl (code_val c) 16)) by lia.
    rewrite (code_word_join c CR).
    zs. zs. change (Z.land (Z.shiftr c 8) 255) with (code_bits c).
    apply K.
  Qed.

  Lemma cl_pull_a : forall (x1 x2 x3 x4 x6 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA lb H B c : Z),
    0 <= c < 256 -> 0 <= B <= 40 -> 0 <= H < 2 ^ B -> 1 <= lb <= 15 -> 0 < TA < 140737488355328 ->
    (forall (x10' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 TA) x6 (Z_to_bv 64 (2 ^ lb - 1)) x8 x9 x10' (Z_to_bv 64 (TA + 4 * ((H + c * 2 ^ B) mod 2 ^ lb))) x12 (Z_to_bv 64 ((H + c * 2 ^ B) mod 2 ^ lb)) x14 x15 x16 x17 x18 x22 x19 x25 x26 (Z_to_bv 64 (H + c * 2 ^ B)) x20 x23 x21 x27 x28 x29 x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fa8c) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 TA) x6 (Z_to_bv 64 (2 ^ lb - 1)) x8 x9 (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 (Z_to_bv 64 H) x20 x23 x21 x27 x28 x29 x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fa70) fc None m (seg_rom bsegs)).
  Proof.
    intros until c. intros HC HB HH LB TAR K.
    pose proof (pow2_le_15 lb ltac:(lia)) as P15. pose proof (pull_bound H B c ltac:(lia) HH HC) as PB. pose proof (pow2_48 (B + 8) ltac:(lia)) as P48.
    pose proof (mod_pow2_bound (H + c * 2 ^ B) lb ltac:(lia)) as MR.
    zs. zs. rewrite (pull_hold H c B) by lia.
    zs. rewrite (root_idx (H + c * 2 ^ B) lb) by lia.
    zs. rewrite shl2.
    zs. replace (4 * ((H + c * 2 ^ B) mod 2 ^ lb) + TA) with (TA + 4 * ((H + c * 2 ^ B) mod 2 ^ lb)) by lia.
    zs. pc_dec_ub.
    apply K.
  Qed.

  Lemma cl_pull_b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x15 x16 x17 x18 x19 x20 x22 x24 x25 x27 x28 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (B av EA NX1 : Z),
    0 <= B <= 40 -> 1 <= av < 67108864 -> 0 < EA < 140737488355328 ->
    (forall (x10' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10' (Z_to_bv 64 NX1) x12 x13 (Z_to_bv 64 NX1) x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 1) x24 x20 (Z_to_bv 64 (- (B + 8))) (Z_to_bv 64 (av - 1)) x27 x28 (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (av - 1)) (Z_to_bv 64 (B + 8))) FR (Z_to_bv 64 0x8f9ec) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 EA) x12 x13 (Z_to_bv 64 NX1) x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 1) x24 x20 (Z_to_bv 64 (- B)) (Z_to_bv 64 av) x27 x28 (Z_to_bv 64 B) (Z_to_bv 64 av) (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fa98) fc None m (seg_rom bsegs)).
  Proof.
    intros until NX1. intros HB HA HE K.
    zs. zsb. zs. zs. zs. zs. zs. zs. zs.
    replace (- B + -8) with (- (B + 8)) by lia. replace (av + -1) with (av - 1) by lia.
    apply K.
  Qed.

  Lemma cl_ck_dec : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A sb : Z),
    0 <= A < 140737488355328 -> (sb = 0 \/ (0 < sb <= 7 /\ A mod 8 + 1 - 1 < sb)) ->
    (forall y : word, evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y (Z_to_bv 64 A) x12 (Z_to_bv 64 sb) x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fa68) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 (Z_to_bv 64 sb) x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fa64) fc None m (seg_rom bsegs)).
  Proof.
    intros until sb. intros AR CK K.
    ck_branchJ 10 0x8fa68 CK. apply K.
  Qed.

  Lemma cl_res_a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (c : Z),
    0 <= c < 4294967296 ->
    (code_val c < 16 -> forall (x10' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10' x11 x12 (Z_to_bv 64 c) x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 (Z_to_bv 64 (code_val c)) x29 x30 x31) FR (Z_to_bv 64 0x8faf0) fc None m (seg_rom bsegs))) ->
    (16 <= code_val c -> forall (x10' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10' x11 x12 (Z_to_bv 64 c) x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 (Z_to_bv 64 (code_val c)) x29 x30 x31) FR (Z_to_bv 64 0x8fb74) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 c) x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fae4) fc None m (seg_rom bsegs)).
  Proof.
    intros until c. intros CR K1 K2.
    pose proof (code_val_range c) as VALR.
    assert (EV : code_val c = c / 65536) by (rewrite <- (code_word_val c CR); rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    zs. zs. rewrite (code_word_val c CR).
    zs. zbr K.
    - apply K2. rewrite Z.shiftr_div_pow2 in K by lia. change (2 ^ 20) with 1048576 in K. rewrite EV. clear - K CR. Z.div_mod_to_equations. lia.
    - apply K1. rewrite Z.shiftr_div_pow2 in K by lia. change (2 ^ 20) with 1048576 in K. rewrite EV. clear - K CR. Z.div_mod_to_equations. lia.
  Qed.

  Lemma cl_rep_disp : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (v B : Z),
    16 <= v < 65536 -> 0 <= B <= 40 ->
    (v = 16 -> forall (x22' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 B) x14 x15 x16 x17 x18 x22' x19 x25 x26 x24 x20 (Z_to_bv 64 (- B)) x21 x27 (Z_to_bv 64 v) x29 x30 x31) FR (Z_to_bv 64 0x8fc04) fc None m (seg_rom bsegs))) ->
    (v = 17 -> forall (x22' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 B) x14 x15 x16 x17 x18 x22' x19 x25 x26 x24 x20 (Z_to_bv 64 (- B)) x21 x27 (Z_to_bv 64 v) x29 x30 x31) FR (Z_to_bv 64 0x8fb88) fc None m (seg_rom bsegs))) ->
    (v <> 16 /\ v <> 17 -> forall (x22' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 B) x14 x15 x16 x17 x18 x22' x19 x25 x26 x24 x20 (Z_to_bv 64 (- B)) x21 x27 (Z_to_bv 64 v) x29 x30 x31) FR (Z_to_bv 64 0x8fc80) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 (Z_to_bv 64 (- B)) x21 x27 (Z_to_bv 64 v) x29 x30 x31) FR (Z_to_bv 64 0x8fb74) fc None m (seg_rom bsegs)).
  Proof.
    intros until B. intros VR BR K16 K17 K18.
    zs. zs. rewrite (negw_neg B) by lia.
    zs. zbr KA.
    - apply K16. lia.
    - zs. zs. zbr KB.
      + apply K18. lia.
      + apply K17. lia.
  Qed.

  Lemma cl_sym_g : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (hb : Z),
    0 <= hb <= 63 ->
    (forall (x11' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11' x12 x13 (Z_to_bv 64 hb) x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fafc) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 hb) x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8faf0) fc None m (seg_rom bsegs)).
  Proof.
    intros until hb. intros HB K.
    zrunu [0x8fafc].
    apply K.
  Qed.

  Lemma cl_sym_b1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (j : Z),
    0 <= j < 320 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 319) x12 x13 (Z_to_bv 64 (j + 1)) x15 (Z_to_bv 64 j) x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fb0c) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 j) x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fb04) fc None m (seg_rom bsegs)).
  Proof.
    intros until j. intros HJ K.
    zs. zs.
    exact K.
  Qed.

  Lemma cl_sym_b2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (j : Z),
    0 <= j < 320 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (2 * j)) x12 x13 x14 x15 (Z_to_bv 64 j) x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fb20) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 319) x12 x13 x14 x15 (Z_to_bv 64 j) x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fb14) fc None m (seg_rom bsegs)).
  Proof.
    intros until j. intros HJ K.
    zrunu [0x8fb1c]. zs. rewrite Z.shiftl_mul_pow2 by lia. replace (j * 2 ^ 1) with (2 * j) by lia.
    exact K.
  Qed.

  Lemma cl_sym_b3 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (LA j : Z),
    0 < LA < 140737488355328 -> 0 <= j < 320 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (18446744073709551615 - LA)) (Z_to_bv 64 (2 * j)) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fb2c) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (18446744073709551615 - LA)) (Z_to_bv 64 (2 * j)) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fb24) fc None m (seg_rom bsegs)).
  Proof.
    intros until j. intros HL HJ K.
    zrunu [0x8fb2c].
    exact K.
  Qed.

  Lemma cl_sym_drop : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (H B c : Z),
    0 <= c < 4294967296 -> 1 <= code_bits c <= 15 -> 0 <= H < 2 ^ B -> code_bits c <= B -> B <= 40 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (B - code_bits c)) x11 x12 (Z_to_bv 64 (code_bits c)) x14 x15 (Z_to_bv 64 B) x17 x18 x22 (Z_to_bv 64 (Z.shiftr c 8)) x25 x26 (Z_to_bv 64 (H / 2 ^ code_bits c)) x20 (Z_to_bv 64 (- B)) x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fb58) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 c) x14 x15 x16 x17 x18 x22 (Z_to_bv 64 (Z.shiftr c 8)) x25 x26 (Z_to_bv 64 H) x20 (Z_to_bv 64 (- B)) x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fb44) fc None m (seg_rom bsegs)).
  Proof.
    intros until c. intros CR CB HH HB B40 K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40. pose proof (cw_shr8_range c CR) as S8R.
    zs. rewrite ?(Z.mod_small (Z.shiftr c 8) 18446744073709551616) by lia. rewrite (cw_mod64 c) by lia. rewrite <- (Z.mod_small (code_bits c) 64) at 1 by lia. rewrite (srl_div H (code_bits c)) by lia.
    zs. zs. rewrite (negw_neg B) by lia. zs. rewrite (shl48_shr56 c CR). zs.
    exact K.
  Qed.

  Lemma cl_rg17 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A B av : Z),
    1 <= A < 140737488355328 -> 0 <= B <= 40 ->
    (forall (x28' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 av) (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 (A + 1)) x24 x20 x23 (Z_to_bv 64 av) x27 x28' x29 x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fbbc) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 (Z_to_bv 64 av) x27 x28 x29 x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fb9c) fc None m (seg_rom bsegs)).
  Proof.
    intros until av. intros HA HB K.
    zrunu [0x8fbbc].
    apply K.
  Qed.

  Lemma cl_rck17 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A sb : Z),
    0 <= A < 140737488355328 -> (sb = 0 \/ (0 < sb <= 7 /\ A mod 8 + 1 - 1 < sb)) ->
    (forall y : word, evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 y x21 x27 (Z_to_bv 64 sb) x29 x30 x31) FR (Z_to_bv 64 0x8fbcc) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 (Z_to_bv 64 sb) x29 x30 x31) FR (Z_to_bv 64 0x8fbc8) fc None m (seg_rom bsegs)).
  Proof.
    intros until sb. intros AR CK K.
    (* [U14B] A2 2026-11-12: the 1.4 check temp is s9 = x25 (0x8fc30 and s9,a1,7), as mover had it *)
    ck_branchJ 25 0x8fbcc CK. apply K.
  Qed.

  Lemma cl_radv17 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x30 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (D n ci H B c : Z),
    0 <= c < 256 -> 0 <= B <= 40 -> 0 <= H < 2 ^ B -> 0 <= ci < n -> n < 67108864 -> 0 <= D < 140737488355328 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (n - ci)) (Z_to_bv 64 (D + (ci + 1))) x12 (Z_to_bv 64 (D + (ci + 1))) x14 x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 (D + (ci + 1))) (Z_to_bv 64 (H + c * 2 ^ B)) x20 x26 (Z_to_bv 64 (n - (ci + 1))) x27 (Z_to_bv 64 (D + (ci + 1))) (Z_to_bv 64 (B + 8)) x30 (Z_to_bv 64 (B + 8))) FR (Z_to_bv 64 0x8fbf0) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (n - ci)) (Z_to_bv 64 c) x12 (Z_to_bv 64 (D + ci)) x14 x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 (D + ci + 1)) (Z_to_bv 64 H) x20 x26 x21 x27 x28 (Z_to_bv 64 B) x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fbd0) fc None m (seg_rom bsegs)).
  Proof.
    intros until c. intros HC HB HH HCI HN HD K.
    pose proof (pull_bound H B c ltac:(lia) HH HC) as PB. pose proof (pow2_48 (B + 8) ltac:(lia)) as P48.
    zs. zs. zs. zs. zs. rewrite (pull_hold H c B) by lia.
    zs. zs. zs.
    replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
    exact K.
  Qed.

  Lemma cl_rg18 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A B av : Z),
    1 <= A < 140737488355328 -> 0 <= B <= 40 ->
    (forall (x28' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 av) (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 (A + 1)) x24 x20 x23 (Z_to_bv 64 av) x27 x28' x29 x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fcb4) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 (Z_to_bv 64 av) x27 x28 x29 x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fc94) fc None m (seg_rom bsegs)).
  Proof.
    intros until av. intros HA HB K.
    zrunu [0x8fcb4].
    apply K.
  Qed.

  Lemma cl_rck18 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A sb : Z),
    0 <= A < 140737488355328 -> (sb = 0 \/ (0 < sb <= 7 /\ A mod 8 + 1 - 1 < sb)) ->
    (forall y : word, evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 y x21 x27 (Z_to_bv 64 sb) x29 x30 x31) FR (Z_to_bv 64 0x8fcc4) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 (Z_to_bv 64 sb) x29 x30 x31) FR (Z_to_bv 64 0x8fcc0) fc None m (seg_rom bsegs)).
  Proof.
    intros until sb. intros AR CK K.
    ck_branchJ 25 0x8fcc4 CK. apply K.
  Qed.

  Lemma cl_radv18 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x30 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (D n ci H B c : Z),
    0 <= c < 256 -> 0 <= B <= 40 -> 0 <= H < 2 ^ B -> 0 <= ci < n -> n < 67108864 -> 0 <= D < 140737488355328 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (n - ci)) (Z_to_bv 64 (D + (ci + 1))) x12 (Z_to_bv 64 (D + (ci + 1))) x14 x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 (D + (ci + 1))) (Z_to_bv 64 (H + c * 2 ^ B)) x20 x26 (Z_to_bv 64 (n - (ci + 1))) x27 (Z_to_bv 64 (D + (ci + 1))) (Z_to_bv 64 (B + 8)) x30 (Z_to_bv 64 (B + 8))) FR (Z_to_bv 64 0x8fce8) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (n - ci)) (Z_to_bv 64 c) x12 (Z_to_bv 64 (D + ci)) x14 x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 (D + ci + 1)) (Z_to_bv 64 H) x20 x26 x21 x27 x28 (Z_to_bv 64 B) x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fcc8) fc None m (seg_rom bsegs)).
  Proof.
    intros until c. intros HC HB HH HCI HN HD K.
    pose proof (pull_bound H B c ltac:(lia) HH HC) as PB. pose proof (pow2_48 (B + 8) ltac:(lia)) as P48.
    zs. zs. zs. zs. zs. rewrite (pull_hold H c B) by lia.
    zs. zs. zs.
    replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
    exact K.
  Qed.

  Lemma cl_rg16 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A B av : Z),
    1 <= A < 140737488355328 -> 0 <= B <= 40 ->
    (forall (x28' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 av) (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 (A + 1)) x24 x20 x23 (Z_to_bv 64 av) x27 x28' x29 x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fc38) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 (Z_to_bv 64 av) x27 x28 x29 x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fc18) fc None m (seg_rom bsegs)).
  Proof.
    intros until av. intros HA HB K.
    zrunu [0x8fc38].
    apply K.
  Qed.

  Lemma cl_rck16 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A sb : Z),
    0 <= A < 140737488355328 -> (sb = 0 \/ (0 < sb <= 7 /\ A mod 8 + 1 - 1 < sb)) ->
    (forall y : word, evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 y x21 x27 (Z_to_bv 64 sb) x29 x30 x31) FR (Z_to_bv 64 0x8fc48) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 (Z_to_bv 64 sb) x29 x30 x31) FR (Z_to_bv 64 0x8fc44) fc None m (seg_rom bsegs)).
  Proof.
    intros until sb. intros AR CK K.
    ck_branchJ 25 0x8fc48 CK. apply K.
  Qed.

  Lemma cl_radv16 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x30 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (D n ci H B c : Z),
    0 <= c < 256 -> 0 <= B <= 40 -> 0 <= H < 2 ^ B -> 0 <= ci < n -> n < 67108864 -> 0 <= D < 140737488355328 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (n - ci)) (Z_to_bv 64 (D + (ci + 1))) x12 (Z_to_bv 64 (D + (ci + 1))) x14 x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 (D + (ci + 1))) (Z_to_bv 64 (H + c * 2 ^ B)) x20 x26 (Z_to_bv 64 (n - (ci + 1))) x27 (Z_to_bv 64 (D + (ci + 1))) (Z_to_bv 64 (B + 8)) x30 (Z_to_bv 64 (B + 8))) FR (Z_to_bv 64 0x8fc6c) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (n - ci)) (Z_to_bv 64 c) x12 (Z_to_bv 64 (D + ci)) x14 x15 x16 x17 x18 x22 x19 x25 (Z_to_bv 64 (D + ci + 1)) (Z_to_bv 64 H) x20 x26 x21 x27 x28 (Z_to_bv 64 B) x30 (Z_to_bv 64 B)) FR (Z_to_bv 64 0x8fc4c) fc None m (seg_rom bsegs)).
  Proof.
    intros until c. intros HC HB HH HCI HN HD K.
    pose proof (pull_bound H B c ltac:(lia) HH HC) as PB. pose proof (pow2_48 (B + 8) ltac:(lia)) as P48.
    zs. zs. zs. zs. zs. rewrite (pull_hold H c B) by lia.
    zs. zs. zs.
    replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
    exact K.
  Qed.

  Lemma cl_x17 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x27 x28 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (H B c : Z),
    0 <= c < 4294967296 -> 1 <= code_bits c <= 15 -> 0 <= H < 2 ^ B -> code_bits c + 3 <= B -> B <= 40 ->
    (forall (x11' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11' x12 (Z_to_bv 64 (H / 2 ^ code_bits c mod 8 + 3)) (Z_to_bv 64 (B - code_bits c - 3)) x15 x16 x17 x18 x22 (Z_to_bv 64 (Z.shiftr c 8)) x25 x26 (Z_to_bv 64 (H / 2 ^ code_bits c / 8)) x20 x23 x21 x27 x28 (Z_to_bv 64 B) (Z_to_bv 64 0) x31) FR (Z_to_bv 64 0x8fde0) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 (code_bits c)) x15 x16 x17 x18 x22 (Z_to_bv 64 (Z.shiftr c 8)) x25 x26 (Z_to_bv 64 H) x20 x23 x21 x27 x28 (Z_to_bv 64 B) x30 x31) FR (Z_to_bv 64 0x8fd04) fc None m (seg_rom bsegs)).
  Proof.
    intros until c. intros CR CB HH HB B40 K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40. pose proof (cw_shr8_range c CR) as S8R.
    pose proof (drop_bound H B (code_bits c) ltac:(lia) HH) as DB.
    zrunu [0x8fd10]. zs. zs. rewrite ?(Z.mod_small (Z.shiftr c 8) 18446744073709551616) by lia. rewrite (cw_mod64 c) by lia. rewrite <- (Z.mod_small (code_bits c) 64) at 1 by lia. rewrite (srl_div H (code_bits c)) by lia.
    zs. zs. replace (Z.land (H / 2 ^ code_bits c) 7) with (H / 2 ^ code_bits c mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    zs. rewrite (Z.shiftr_div_pow2 (H / 2 ^ code_bits c) 3) by lia. change (2 ^ 3) with 8.
    zs. zs. zs.
    replace (B - code_bits c + -3) with (B - code_bits c - 3) by lia.
    apply K.
  Qed.

  Lemma cl_x18 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x27 x28 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (H B c : Z),
    0 <= c < 4294967296 -> 1 <= code_bits c <= 15 -> 0 <= H < 2 ^ B -> code_bits c + 7 <= B -> B <= 40 ->
    (forall (x11' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11' x12 (Z_to_bv 64 (H / 2 ^ code_bits c mod 128 + 11)) (Z_to_bv 64 (B - code_bits c - 7)) x15 x16 x17 x18 x22 (Z_to_bv 64 (Z.shiftr c 8)) x25 x26 (Z_to_bv 64 (H / 2 ^ code_bits c / 128)) x20 x23 x21 x27 x28 (Z_to_bv 64 B) (Z_to_bv 64 0) x31) FR (Z_to_bv 64 0x8fde0) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 (code_bits c)) x15 x16 x17 x18 x22 (Z_to_bv 64 (Z.shiftr c 8)) x25 x26 (Z_to_bv 64 H) x20 x23 x21 x27 x28 (Z_to_bv 64 B) x30 x31) FR (Z_to_bv 64 0x8fdb8) fc None m (seg_rom bsegs)).
  Proof.
    intros until c. intros CR CB HH HB B40 K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40. pose proof (cw_shr8_range c CR) as S8R.
    pose proof (drop_bound H B (code_bits c) ltac:(lia) HH) as DB.
    zrunu [0x8fdc4]. zs. zs. rewrite ?(Z.mod_small (Z.shiftr c 8) 18446744073709551616) by lia. rewrite (cw_mod64 c) by lia. rewrite <- (Z.mod_small (code_bits c) 64) at 1 by lia. rewrite (srl_div H (code_bits c)) by lia.
    zs. zs. replace (Z.land (H / 2 ^ code_bits c) 127) with (H / 2 ^ code_bits c mod 128) by (change 127 with (Z.ones 7); rewrite Z.land_ones by lia; reflexivity).
    zs. rewrite (Z.shiftr_div_pow2 (H / 2 ^ code_bits c) 7) by lia. change (2 ^ 7) with 128.
    zs. zs.
    replace (B - code_bits c + -7) with (B - code_bits c - 7) by lia.
    apply K.
  Qed.

  Lemma cl_x16a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x27 x28 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (H B c : Z),
    0 <= c < 4294967296 -> 1 <= code_bits c <= 15 -> 0 <= H < 2 ^ B -> code_bits c <= B -> B <= 40 ->
    (forall (x11' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (B - code_bits c)) x11' x12 x13 (Z_to_bv 64 (code_bits c)) x15 x16 x17 x18 x22 (Z_to_bv 64 (Z.shiftr c 8)) x25 x26 (Z_to_bv 64 (H / 2 ^ code_bits c)) x20 x23 x21 x27 x28 (Z_to_bv 64 B) x30 x31) FR (Z_to_bv 64 0x8fd4c) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 (code_bits c)) x15 x16 x17 x18 x22 (Z_to_bv 64 (Z.shiftr c 8)) x25 x26 (Z_to_bv 64 H) x20 x23 x21 x27 x28 (Z_to_bv 64 B) x30 x31) FR (Z_to_bv 64 0x8fd38) fc None m (seg_rom bsegs)).
  Proof.
    intros until c. intros CR CB HH HB B40 K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40. pose proof (cw_shr8_range c CR) as S8R.
    zrunu [0x8fd44]. zs. rewrite ?(Z.mod_small (Z.shiftr c 8) 18446744073709551616) by lia. rewrite (cw_mod64 c) by lia. rewrite <- (Z.mod_small (code_bits c) 64) at 1 by lia. rewrite (srl_div H (code_bits c)) by lia.
    zs.
    apply K.
  Qed.

  Lemma cl_x16b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (j : Z),
    1 <= j < 320 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (2 * (j - 1))) x12 x13 x14 x15 (Z_to_bv 64 j) x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fd6c) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 j) x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fd58) fc None m (seg_rom bsegs)).
  Proof.
    intros until j. intros HJ K.
    zrunu [0x8fd64]. zs. zs. rewrite Z.shiftl_mul_pow2 by lia. replace ((j + -1) * 2 ^ 1) with (2 * (j - 1)) by lia.
    exact K.
  Qed.

  Lemma cl_x16g : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (LA k : Z),
    0 < LA < 140737488355328 -> 0 <= k < 640 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (18446744073709551615 - LA)) (Z_to_bv 64 k) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fd78) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (18446744073709551615 - LA)) (Z_to_bv 64 k) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fd70) fc None m (seg_rom bsegs)).
  Proof.
    intros until k. intros HL HK K.
    zrunu [0x8fd78].
    exact K.
  Qed.

  Lemma cl_x16c : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (H : Z),
    0 <= H < 18446744073709551616 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (H mod 4 + 3)) x14 x15 x16 x17 x18 x22 x19 x25 x26 (Z_to_bv 64 (H / 4)) x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fda0) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 (Z_to_bv 64 H) x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fd94) fc None m (seg_rom bsegs)).
  Proof.
    intros until H. intros HH K.
    zs. replace (Z.land H 3) with (H mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
    zs. zs. rewrite (Z.shiftr_div_pow2 H 2) by lia. change (2 ^ 2) with 4.
    exact K.
  Qed.

  Lemma cl_chk_a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (cp j T : Z),
    0 <= cp < 65536 -> 0 <= j < 65536 -> 0 <= T < 65536 ->
    (j + cp <= T -> evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 320) x12 (Z_to_bv 64 cp) (Z_to_bv 64 j) x15 (Z_to_bv 64 j) (Z_to_bv 64 T) x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fdf8) fc None m (seg_rom bsegs))) ->
    (T < j + cp -> forall (x11' : word), evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11' x12 (Z_to_bv 64 cp) x14 x15 (Z_to_bv 64 j) (Z_to_bv 64 T) x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x92764) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 cp) x14 x15 (Z_to_bv 64 j) (Z_to_bv 64 T) x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fde4) fc None m (seg_rom bsegs)).
  Proof.
    intros until T. intros HC HJ HT K1 K2.
    zs. zs. zbr KA.
    - zs. zs. apply K1. lia.
    - zs. apply K2. lia.
  Qed.

  Lemma cl_chk_b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (j : Z),
    0 <= j <= 320 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 320) x12 x13 (Z_to_bv 64 320) x15 (Z_to_bv 64 j) x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fe04) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 320) x12 x13 x14 x15 (Z_to_bv 64 j) x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fdfc) fc None m (seg_rom bsegs)).
  Proof.
    intros until j. intros HJ K.
    zrunu [0x8fe04].
    exact K.
  Qed.

  Lemma cl_fill_g : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (k : Z),
    0 <= k < 320 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (2 * k)) x12 x13 (Z_to_bv 64 320) x15 (Z_to_bv 64 k) x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fe10) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 320) x15 (Z_to_bv 64 k) x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8fe04) fc None m (seg_rom bsegs)).
  Proof.
    intros until k. intros HK K.
    zrunu [0x8fe0c]. zs. rewrite Z.shiftl_mul_pow2 by lia. replace (k * 2 ^ 1) with (2 * k) by lia.
    exact K.
  Qed.

  Lemma cl_fill_g2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (LA k2 : Z),
    0 < LA < 140737488355328 -> 0 <= k2 < 640 ->
    (evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 k2) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 (Z_to_bv 64 (18446744073709551615 - LA)) x30 x31) FR (Z_to_bv 64 0x8fe1c) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 k2) x12 x13 x14 x15 x16 x17 x18 x22 x19 x25 x26 x24 x20 x23 x21 x27 x28 (Z_to_bv 64 (18446744073709551615 - LA)) x30 x31) FR (Z_to_bv 64 0x8fe14) fc None m (seg_rom bsegs)).
  Proof.
    intros until k2. intros HL HK K.
    zrunu [0x8fe1c].
    exact K.
  Qed.

End S.
End CANSEC1.
