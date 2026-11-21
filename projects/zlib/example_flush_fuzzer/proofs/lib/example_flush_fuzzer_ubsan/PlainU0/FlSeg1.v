(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool Logic.FunctionalExtensionality.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Tac Image ZBridge Walk Arr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CkP Require Import RegsFull BridgeKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import PImg FlKit F_memset.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section SEG.
Context {rc : runConstT}.
Variable usp : Z.
Hypothesis USP : 0x7fff7f800000 <= usp < 2^64.
Hypothesis USP16 : usp mod 16 = 0.
Definition TFC (p0 : list byte) (st : cell) (p96 : list byte) (v19 : word) (up cp n : Z) : list cell :=
  [CB 56 p0; C8 (Z_to_bv 64 0); st; C8 (Z_to_bv 64 0x1a9f4); C8 (Z_to_bv 64 0x1aa04); C8 (Z_to_bv 64 0); CB 24 p96;
   C8 v19; C8 (Z_to_bv 64 cp); C8 (Z_to_bv 64 up); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0x1635c)].
Definition LFC (pad : list byte) (cl : Z) (v18 v9 v8 v1 : word) : list cell :=
  [CB 8 pad; C8 (Z_to_bv 64 cl); C8 v18; C8 v9; C8 v8; C8 v1].

Lemma fl_seg_entry : forall (Q : machine_state -> Prop) (D n lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (old : list byte)
    (x1 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -48 -> 0 <= lo -> 4 <= n <= 2^20 -> 0 <= D < 2^64 ->
  stk psegs M lo usp -> mem_inv psegs M ->
  rw_cells psegs M 0x3d6a0 [CB 16 old] ->
  (forall (M1 : word -> option byte) (y12 y13 : word) (pad : list byte),
     munch [(usp + -48, usp); (0x3d6a0, 0x3d6b0)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -48) ->
     rw_cells psegs M1 (usp + -48) (LFC pad (fl_cl n) x18 x9 x8 x1) ->
     rw_cells psegs M1 0x3d6a0 [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 D)] ->
     Q (MS (mkR (Z_to_bv 64 0x16334) (Z_to_bv 64 (usp + -48)) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 D)
                (Z_to_bv 64 1) (Z_to_bv 64 (fl_cl n)) y12 y13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x23844) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 usp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 D) (Z_to_bv 64 n) x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x162d8) fc None M (seg_rom psegs)).
Proof using USP.
  intros Q D n lo M F fc old x1 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 NR DR ST MI STAT HK.
  change (2^20) with 1048576 in NR.
  pose proof (fl_cb_range n ltac:(lia)) as CBR. change (2^21) with 2097152 in CBR.
  pose proof (munch_refl [(usp + -48, usp); (0x3d6a0, 0x3d6b0)] M) as MU.
  pose proof (wmono_refl psegs M) as WM.
  unfold LFC in HK.
  step. carve_frame 48%nat ST. do 4 step. do 3 step.
  step. do 11 step.
  rewrite !unsigned_lit by lia. rewrite !Z.shiftr_div_pow2 by lia.
  replace (n + n / 2 ^ 12 + (n / 2 ^ 14 + n / 2 ^ 25) + 13) with (fl_cb n)
    by (unfold fl_cb; change (2^12) with 4096; change (2^14) with 16384; change (2^25) with 33554432; lia).
  do 7 step.
  step.
  match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota|] end.
  2:{ symmetry. unfold bv_ltu. rewrite !unsigned_lit_wrap. apply Z.ltb_ge. change (2^64) with 18446744073709551616. lia. }
  (* 1.4: the bound is or-ed with (0 - sltu fl_cb n n); that sltu is 0 because n <= fl_cb n *)
  assert (LEN : n <= fl_cb n) by (unfold fl_cb; change (2^12) with 4096; change (2^14) with 16384; change (2^25) with 33554432; lia).
  assert (VS : v_sltu (Z_to_bv 64 (fl_cb n)) (Z_to_bv 64 n) = Z_to_bv 64 0).
  { rewrite v_sltu_b2z, !unsigned_lit by lia.
    replace (fl_cb n <? n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  assert (VZ0 : bv_unsigned (Z_to_bv 64 0) = 0) by (apply unsigned_lit; lia).
  assert (VL : Z.lor (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 0)))) (bv_unsigned (Z_to_bv 64 (fl_cb n)))
               = bv_unsigned (Z_to_bv 64 (fl_cb n))).
  { rewrite VZ0. change (0 - 0) with 0. rewrite VZ0. apply Z.lor_0_l. }
  assert (VU : bv_unsigned (Z_to_bv 64 (fl_cb n)) = fl_cb n) by (apply unsigned_lit; lia).
  rewrite VS in *. rewrite VL in *. rewrite VU in *.
  do 6 step.
  replace (Z.shiftl (bv_unsigned (Z_to_bv 64 (fl_cb n))) 1 + 100) with (fl_cl n) in *
    by (rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; unfold fl_cl; lia).
  apply evt_done. eapply HK. all: try eassumption.
Qed.

Lemma fl_seg_reject : forall (Q : machine_state -> Prop) (D n lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -48 -> 0 <= lo -> (0 <= n <= 3 \/ 2^20 < n < 2^64) -> 0 <= D < 2^64 ->
  stk psegs M lo usp -> mem_inv psegs M ->
  (forall (M1 : word -> option byte) (y11 y12 y13 : word),
     munch [(usp + -48, usp)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo usp ->
     Q (MS (mkR x1 (Z_to_bv 64 usp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) y11 y12 y13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (ret_pc x1) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 usp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 D) (Z_to_bv 64 n) x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x162d8) fc None M (seg_rom psegs)).
Proof using USP.
  intros Q D n lo M F fc x1 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 NR DR ST MI HK.
  change (2^20) with 1048576 in NR. change (2^64) with 18446744073709551616 in NR.
  pose proof (munch_refl [(usp + -48, usp)] M) as MU.
  pose proof (wmono_refl psegs M) as WM.
  step. carve_frame 48%nat ST. do 4 step. do 3 step.
  step. do 11 step.
  do 7 step.
  step.
  match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota|] end.
  2:{ symmetry. unfold bv_ltu. rewrite !unsigned_lit_wrap. apply Z.ltb_lt. change (2^64) with 18446744073709551616.
      rewrite ?unsigned_lit by lia. lia. }
  do 5 step. step. release_frame FR ST usp. step.
  apply evt_done. eapply HK; eassumption.
Qed.

Lemma fl_seg_c1 : forall (Q : machine_state -> Prop) (n cp : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 < cp < 2^64 -> 0 <= n < 2^64 ->
  Q (MS (mkR (Z_to_bv 64 0x16344) x2 x3 x4 x5 x6 x7 (Z_to_bv 64 n) x9 (Z_to_bv 64 1) (Z_to_bv 64 n) x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 cp) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x23844) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 n) x9 (Z_to_bv 64 cp) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16334) fc None M (seg_rom psegs)).
Proof using usp.
  intros Q n cp M F fc x1 x2 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 CP NR HK.
  change (2^64) with 18446744073709551616 in CP.
  do 4 step. apply evt_done. exact HK.
Qed.

Lemma fl_seg_tf1 : forall (Q : machine_state -> Prop) (D n cp up lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -288 -> 0 <= lo -> 4 <= n <= 2^20 -> 0 < cp < 2^64 -> 0 < up < 2^64 -> 0 <= D < 2^64 ->
  stk psegs M lo (usp + -48) -> mem_inv psegs M -> relro_pristine M ->
  rw_cells psegs M 0x3d6a0 [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 D)] ->
  (forall (M1 : word -> option byte) (p0 p64 p96 q0 : list byte),
     munch [(usp + -288, usp + -48)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -288) ->
     rw_cells psegs M1 (usp + -208) (TFC p0 (CB 8 p64) p96 x19 up cp n) ->
     rw_cells psegs M1 (usp + -288) [CB 8 q0; C8 x23; C8 x22; C8 x21; C8 x20; C8 (Z_to_bv 64 0x3d6a0); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 cp);
                                   C8 (Z_to_bv 64 (usp + -40)); C8 (Z_to_bv 64 0x16028)] ->
     rw_cells psegs M1 0x3d6a0 [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 D)] ->
     Q (MS (mkR (Z_to_bv 64 0x16524) (Z_to_bv 64 (usp + -288)) x3 x4 (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 (-8)) x7
                (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 cp) (Z_to_bv 64 5968) (Z_to_bv 64 1) (Z_to_bv 64 5968) (Z_to_bv 64 15) (Z_to_bv 64 8)
                (Z_to_bv 64 0) (Z_to_bv 64 0x1a9f4) (Z_to_bv 64 0)
                (Z_to_bv 64 5968) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x23abc) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -48)) x3 x4 x5 x6 x7 (Z_to_bv 64 n) x9 (Z_to_bv 64 up) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 cp) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16344) fc None M (seg_rom psegs)).
Proof using USP USP16.
  intros Q D n cp up lo M F fc x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 NR CP UP DR ST MI RP STAT HK.
  change (2^20) with 1048576 in NR. change (2^64) with 18446744073709551616 in CP, UP, DR.
  pose proof (fl_cb_range n ltac:(lia)) as CBR. change (2^21) with 2097152 in CBR.
  pose proof (munch_refl [(usp + -288, usp + -48)] M) as MU.
  pose proof (wmono_refl psegs M) as WM.
  relro_cells RP. unfold TFC in HK.
  step. step. br_false. step. br_false. do 3 step.
  step. carve_frame 160%nat ST. replace (usp + -48 + -160) with (usp + -208) in * by lia.
  do 5 step. do 2 step. do 2 step. step. do 3 step. do 6 step.
  do 7 step.
  step. carve_frame 80%nat ST. replace (usp + -208 + -80) with (usp + -288) in * by lia.
  do 9 step. (* 1.4 UBSan: deflateInit2_ saves s7 too (80-byte frame) *)
  do 3 step. if_false. do 2 step. if_false. do 3 step. if_false. do 2 step. br_false.
  do 2 step. br_align8.
  do 3 step. if_true. do 6 step. if_false. do 5 step. if_false.
  do 2 step. if_true. do 2 step. if_true. do 4 step. if_false.
  do 2 step. if_false. do 2 step. if_false. do 3 step. if_false. do 3 step. if_false.
  do 4 step. rewrite Z.land_0_r. if_false.
  do 5 step. if_true.
  do 8 step. do 4 step. (* 1.4 UBSan: + mv a2,s2 before the zalloc call *)
  apply evt_done. eapply HK; eassumption.
Qed.

(* zl14 helper (unit f-compressBound): a heap byte-run read at a window address; the window lies in the
   calloc'd block, outside the image (ref_mrd_overlay), so mrd is the memory itself *)
Lemma zfill_read (m : word -> option byte) (A : Z) (bs : list byte) (z : byte) (i : Z) :
  bytes_at psegs m A bs -> (forall j, (j < length bs)%nat -> nth_error bs j = Some z) ->
  0 <= i < Z.of_nat (length bs) -> mrd psegs m (wa (A + i)) = Some z.
Proof.
  intros HB Hz Hi. destruct HB as (_ & _ & HB).
  assert (Hn : Z.of_nat (Z.to_nat i) = i) by (apply Z2Nat.id; lia).
  assert (Hl : (Z.to_nat i < length bs)%nat) by lia.
  pose proof (HB _ Hl) as E. rewrite Hn in E. rewrite (Hz _ Hl) in E. exact E.
Qed.

Lemma zfill_pw (M m' : word -> option byte) (A A' : Z) (bs bs' : list byte) (z : byte) (x : word) :
  bytes_at psegs M A bs -> bytes_at psegs m' A' bs' ->
  (forall j, (j < length bs)%nat -> nth_error bs j = Some z) ->
  (forall j, (j < length bs')%nat -> nth_error bs' j = Some z) ->
  A <= bv_unsigned x -> bv_unsigned x < A + Z.of_nat (length bs) ->
  A' <= bv_unsigned x -> bv_unsigned x < A' + Z.of_nat (length bs') ->
  (bv_unsigned x + 1 <= 0x10000 \/ 0x5f000 <= bv_unsigned x)%Z -> M x = m' x.
Proof.
  intros HM HM' Hz Hz' Hlo Hhi Hlo' Hhi' Hov.
  assert (Hw : forall B, wa (B + (bv_unsigned x - B)) = x).
  { intro B. replace (B + (bv_unsigned x - B)) with (bv_unsigned x) by lia. unfold wa. apply Z_to_bv_bv_unsigned. }
  pose proof (zfill_read M A bs z (bv_unsigned x - A) HM Hz ltac:(lia)) as E1.
  pose proof (zfill_read m' A' bs' z (bv_unsigned x - A') HM' Hz' ltac:(lia)) as E2.
  rewrite (Hw A) in E1. rewrite (Hw A') in E2.
  rewrite (ref_mrd_overlay M x Hov) in E1. rewrite (ref_mrd_overlay m' x Hov) in E2.
  congruence.
Qed.

(* zl14 helper (unit f-compressBound): re-chunk a cell list with the same bytes and size *)
Lemma rw_cells_rebytes (m : word -> option byte) (A0 : Z) (cs cs' : list cell) :
  rw_cells psegs m A0 cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells psegs m A0 cs'.
Proof. intros [[W B] WR] WF EB ES. split; [split; [exact WF| rewrite EB; exact B]| rewrite ES; exact WR]. Qed.

Lemma fl_seg_s_ok : forall (Q : machine_state -> Prop) (n cp up s : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (p0 p64 p96 : list byte) (v19 : word)
    (x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  1 <= n <= 2^20 -> 0 < cp < 2^64 -> 0 < up < 2^64 ->
  0 < s -> s + 5968 <= usp - 16384 -> (s + 5968 <= 0x10000 \/ 0x5f000 <= s) -> s mod 16 = 0 ->
  rw_cells psegs M (usp + -208) (TFC p0 (CB 8 p64) p96 v19 up cp n) ->
  rw_cells psegs M s [CB (Z.to_nat 5968) (repeat (Z_to_bv 8 0) (Z.to_nat 5968))] -> mem_inv psegs M ->
  (* 1.4 UBSan: deflateInit2_ zeroes the whole state with memset(s, 0, 5968) right after its zalloc (`jal
     memset` at 0x164dc, as in dict's UBSan build); the zalloc'd block is already zero, so the memset changes no byte
     and the munch names only the fields stored after it. memset leaves t1 / t2 / a3 / a4 / t3-t6 fresh (y6 y7 y13 y14
     y28-y31). Registers at the window zalloc: s2 = s + 5888, s3..s7 = strategy, level, wrap, memLevel, windowBits;
     t0 = w_mask, a7 = the hash_shift product. *)
  (forall (M1 : word -> option byte) (g12 g52 g64 g92 g148 j2 j3 : list byte) (y6 y7 y13 y14 y28 y29 y30 y31 : word),
     munch [(usp + -144, usp + -136); (s, s + 12); (s + 48, s + 52); (s + 56, s + 64); (s + 80, s + 92); (s + 132, s + 148)] M M1 ->
     wmono psegs M M1 -> mem_inv psegs M1 ->
     rw_cells psegs M1 (usp + -208) (TFC p0 (C8 (Z_to_bv 64 s)) p96 v19 up cp n) ->
     rw_cells psegs M1 s [C8 (Z_to_bv 64 (usp + -200)); C4 (Z_to_bv 64 42); CB 36 g12; C4 (Z_to_bv 64 1); CB 4 g52; C8 (Z_to_bv 64 0); CB 16 g64;
                          C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); CB 40 g92;
                          C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); C4 (Z_to_bv 64 5); CB 12 g148] ->
     rw_cells psegs M1 (s + 160) [CB (Z.to_nat 5728) j2] ->
     rw_cells psegs M1 (s + 5888) [CB (Z.to_nat 80) j3] ->
     Q (MS (mkR (Z_to_bv 64 0x165c4) (Z_to_bv 64 (usp + -288)) x3 x4 (Z_to_bv 64 32767) y6 y7
                (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 s) (Z_to_bv 64 65536) (Z_to_bv 64 32768) (Z_to_bv 64 2) y13 y14
                (Z_to_bv 64 42) (Z_to_bv 64 0x1a9f4) (Z_to_bv 64 2907)
                (Z_to_bv 64 (s + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) x24 x25 x26 x27 y28 y29 y30 y31)
           F (Z_to_bv 64 0x23abc) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR (Z_to_bv 64 0x16524) (Z_to_bv 64 (usp + -288)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 cp) (Z_to_bv 64 s) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 5968) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16524) fc None M (seg_rom psegs)).
Proof.
  intros Q n cp up s M F fc p0 p64 p96 v19 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30 x31
         NR CP UP S0 SHI SIMG S16 TD BS MI HK.
  change (2^20) with 1048576 in NR. change (2^64) with 18446744073709551616 in CP, UP.
  pose proof (fl_cb_range n ltac:(lia)) as CBR. change (2^21) with 2097152 in CBR.
  unfold TFC in *.
  (* mv s1,a0; li a0,-4; beqz s1 (falls); mv a0,s1; li a1,0; mv a2,s2; jal memset *)
  do 3 step. br_false. do 4 step.
  eapply evt_cut. { eapply (memset_spec _ _ x3 x4); [ | exact MI ]. rewrite !unsigned_lit by lia. exact BS. }
  cbv beta. intros ms' PO. unfold memset_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mz & -> & MUz & WMz & MIz & ZB).
  rewrite !unsigned_lit in MUz, ZB by lia.
  rewrite Z.mod_0_l in ZB by lia.
  replace (ret_pc (Z_to_bv 64 0x16540)) with (Z_to_bv 64 0x16540) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (rw_cells_transport psegs _ M mz (usp + -208) _ TD MUz WMz ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as TDz.
  (* the block was zero before the memset (BS) and is zero after it (ZB): no byte changed *)
  assert (MU0 : munch [] M mz).
  { intros x _.
    destruct (Z_lt_le_dec (bv_unsigned x) s) as [Lx|Lx]; [apply MUz; cbn [outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (s + 5968)) as [Hx|Hx]; [|apply MUz; cbn [outside]; split; [lia | exact I]].
    pose proof BS as [[_ HB0] _]. pose proof ZB as [[_ HBz] _].
    cbn [cells_bytes cbytes] in HB0, HBz. rewrite app_nil_r in HB0, HBz.
    symmetry. apply (zfill_pw M mz s s _ _ (Z_to_bv 8 0) x HB0 HBz);
      [ intros j Hj; rewrite repeat_length in Hj; apply nth_error_repeat; exact Hj
      | intros j Hj; rewrite repeat_length in Hj; apply nth_error_repeat; exact Hj
      | lia | rewrite repeat_length; lia | lia | rewrite repeat_length; lia | lia ]. }
  clear TD BS.
  destruct (rw_cells_CB_split mz s 5968 160 _ ZB ltac:(lia)) as [B1 B23].
  destruct (rw_cells_CB_split mz (s + 160) (5968 - 160) 5728 _ B23 ltac:(lia)) as [B2 B3]. clear ZB B23.
  change (Z.to_nat 160) with 160%nat in B1. replace (s + 160 + 5728) with (s + 5888) in B3 by lia.
  replace (5968 - 160 - 5728) with 80 in B3 by lia.
  pose proof (conj I MU0) as MUzB. pose proof (conj I WMz) as WMzB. clear MUz MU0 WMz.
  pose proof (munch_refl [(usp + -144, usp + -136); (s, s + 12); (s + 48, s + 52); (s + 56, s + 64); (s + 80, s + 92); (s + 132, s + 148)] mz) as MU.
  pose proof (wmono_refl psegs mz) as WM.
  (* and a1,s1,7; sd s1,56(s0); bnez a1 (s is 16-aligned) *)
  do 3 step. br_align8.
  (* the 30 instructions to the window zalloc (`jalr a6` at 0x16560), then zcalloc's 4 *)
  do 30 step. do 4 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MUt : munch [(usp + -144, usp + -136); (s, s + 12); (s + 48, s + 52); (s + 56, s + 64); (s + 80, s + 92); (s + 132, s + 148)] M mm)
      by (eapply munch_trans; [eapply munch_weaken; [| exact (proj2 MUzB)] | exact MU]; intros x Hx; cbn [outside] in *; exact I);
    assert (WMt : wmono psegs M mm) by (eapply wmono_trans; [exact (proj2 WMzB) | exact WM]) end.
  apply evt_done. eapply HK with (g12 := repeat (Z_to_bv 8 0) 36) (g52 := repeat (Z_to_bv 8 0) 4)
    (g64 := repeat (Z_to_bv 8 0) 16) (g92 := repeat (Z_to_bv 8 0) 40) (g148 := repeat (Z_to_bv 8 0) 12); try eassumption.
  eapply rw_cells_rebytes; [exact B1 | cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; reflexivity | cbn [cells_size csize]; reflexivity].
Qed.

Lemma fl_seg_w : forall (Q : machine_state -> Prop) (n cp up s wnd : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (p0 p96 g12 g52 g64 g92 g148 : list byte) (v19 : word)
    (x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  1 <= n <= 2^20 -> 0 < cp < 2^64 -> 0 < up < 2^64 -> 0 <= wnd < 2^64 ->
  0 < s -> s + 5968 <= usp - 16384 ->
  rw_cells psegs M (usp + -208) (TFC p0 (C8 (Z_to_bv 64 s)) p96 v19 up cp n) ->
  rw_cells psegs M s ([C8 (Z_to_bv 64 (usp + -200)); C4 (Z_to_bv 64 42); CB 36 g12; C4 (Z_to_bv 64 1); CB 4 g52; C8 (Z_to_bv 64 0); CB 16 g64;
                       C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); CB 40 g92;
                       C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); C4 (Z_to_bv 64 5); CB 12 g148]) ->
  mem_inv psegs M ->
  (forall (M1 : word -> option byte) (g92a g104 : list byte),
     munch [(s + 96, s + 104)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     rw_cells psegs M1 (usp + -208) (TFC p0 (C8 (Z_to_bv 64 s)) p96 v19 up cp n) ->
     rw_cells psegs M1 s ([C8 (Z_to_bv 64 (usp + -200)); C4 (Z_to_bv 64 42); CB 36 g12; C4 (Z_to_bv 64 1); CB 4 g52; C8 (Z_to_bv 64 0); CB 16 g64;
                           C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); CB 4 g92a; C8 (Z_to_bv 64 wnd); CB 28 g104;
                           C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); C4 (Z_to_bv 64 5); CB 12 g148]) ->
     Q (MS (mkR (Z_to_bv 64 0x165e0) (Z_to_bv 64 (usp + -288)) x3 x4 x5 x6 x7
                (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 s) (Z_to_bv 64 65536) (Z_to_bv 64 32768) (Z_to_bv 64 2) (Z_to_bv 64 0) (Z_to_bv 64 0x1a9f4)
                x15 x16 x17
                (Z_to_bv 64 (s + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x23abc) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR (Z_to_bv 64 0x165c4) (Z_to_bv 64 (usp + -288)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 s) (Z_to_bv 64 wnd)
                       x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (s + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x165c4) fc None M (seg_rom psegs)).
Proof.
  intros Q n cp up s wnd M F fc p0 p96 g12 g52 g64 g92 g148 v19 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31
         NR CP UP WR S0 SHI TD B1 MI HK.
  change (2^20) with 1048576 in NR. change (2^64) with 18446744073709551616 in CP, UP, WR.
  pose proof (fl_cb_range n ltac:(lia)) as CBR. change (2^21) with 2097152 in CBR.
  pose proof (munch_refl [(s + 96, s + 104)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  unfold TFC in *.
  do 7 step. do 4 step.
  apply evt_done. eapply HK; eassumption.
Qed.

Lemma fl_seg_p : forall (Q : machine_state -> Prop) (n cp up s wnd prv : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (p0 p96 g12 g52 g64 g92a g104 g148 : list byte) (v19 : word)
    (x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  1 <= n <= 2^20 -> 0 < cp < 2^64 -> 0 < up < 2^64 -> 0 <= wnd < 2^64 -> 0 <= prv < 2^64 ->
  0 < s -> s + 5968 <= usp - 16384 ->
  rw_cells psegs M (usp + -208) (TFC p0 (C8 (Z_to_bv 64 s)) p96 v19 up cp n) ->
  rw_cells psegs M s ([C8 (Z_to_bv 64 (usp + -200)); C4 (Z_to_bv 64 42); CB 36 g12; C4 (Z_to_bv 64 1); CB 4 g52; C8 (Z_to_bv 64 0); CB 16 g64;
                       C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); CB 4 g92a; C8 (Z_to_bv 64 wnd); CB 28 g104;
                       C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); C4 (Z_to_bv 64 5); CB 12 g148]) ->
  mem_inv psegs M ->
  (forall (M1 : word -> option byte) (g104a g120 : list byte),
     munch [(s + 112, s + 120)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     rw_cells psegs M1 (usp + -208) (TFC p0 (C8 (Z_to_bv 64 s)) p96 v19 up cp n) ->
     rw_cells psegs M1 s ([C8 (Z_to_bv 64 (usp + -200)); C4 (Z_to_bv 64 42); CB 36 g12; C4 (Z_to_bv 64 1); CB 4 g52; C8 (Z_to_bv 64 0); CB 16 g64;
                           C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); CB 4 g92a; C8 (Z_to_bv 64 wnd); CB 8 g104a;
                           C8 (Z_to_bv 64 prv); CB 12 g120;
                           C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); C4 (Z_to_bv 64 5); CB 12 g148]) ->
     Q (MS (mkR (Z_to_bv 64 0x165fc) (Z_to_bv 64 (usp + -288)) x3 x4 x5 x6 x7
                (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 s) (Z_to_bv 64 65536) (Z_to_bv 64 32768) (Z_to_bv 64 2) (Z_to_bv 64 0) (Z_to_bv 64 0x1a9f4)
                x15 x16 x17
                (Z_to_bv 64 (s + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x23abc) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR (Z_to_bv 64 0x165e0) (Z_to_bv 64 (usp + -288)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 s) (Z_to_bv 64 prv)
                       x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (s + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x165e0) fc None M (seg_rom psegs)).
Proof.
  intros Q n cp up s wnd prv M F fc p0 p96 g12 g52 g64 g92a g104 g148 v19 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31
         NR CP UP WR PR S0 SHI TD B1 MI HK.
  change (2^20) with 1048576 in NR. change (2^64) with 18446744073709551616 in CP, UP, WR, PR.
  pose proof (fl_cb_range n ltac:(lia)) as CBR. change (2^21) with 2097152 in CBR.
  pose proof (munch_refl [(s + 112, s + 120)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  unfold TFC in *.
  do 7 step. do 4 step.
  apply evt_done. eapply HK; eassumption.
Qed.

Lemma fl_seg_h : forall (Q : machine_state -> Prop) (n cp up s wnd prv hd : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (p0 p96 g12 g52 g64 g92a g104a g120 g148 j3 : list byte) (v19 : word)
    (x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  1 <= n <= 2^20 -> 0 < cp < 2^64 -> 0 < up < 2^64 -> 0 <= wnd < 2^64 -> 0 <= prv < 2^64 -> 0 <= hd < 2^64 ->
  0 < s -> s + 5968 <= usp - 16384 ->
  rw_cells psegs M (usp + -208) (TFC p0 (C8 (Z_to_bv 64 s)) p96 v19 up cp n) ->
  rw_cells psegs M s ([C8 (Z_to_bv 64 (usp + -200)); C4 (Z_to_bv 64 42); CB 36 g12; C4 (Z_to_bv 64 1); CB 4 g52; C8 (Z_to_bv 64 0); CB 16 g64;
                       C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); CB 4 g92a; C8 (Z_to_bv 64 wnd); CB 8 g104a;
                       C8 (Z_to_bv 64 prv); CB 12 g120;
                       C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); C4 (Z_to_bv 64 5); CB 12 g148]) ->
  (* 1.4: the state's last block s + 5888 .. s + 5968 is 80 bytes, and high_water's
     zero goes to s + 5952 (`sd zero,64(s4)` at 0x163fc, s4 = s + 5888) *)
  rw_cells psegs M (s + 5888) [CB 80 j3] ->
  mem_inv psegs M ->
  (forall (M1 : word -> option byte) (g128 j3a j3b j3c : list byte),
     munch [(s + 120, s + 128); (s + 5896, s + 5900); (s + 5952, s + 5960)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     rw_cells psegs M1 (usp + -208) (TFC p0 (C8 (Z_to_bv 64 s)) p96 v19 up cp n) ->
     rw_cells psegs M1 s ([C8 (Z_to_bv 64 (usp + -200)); C4 (Z_to_bv 64 42); CB 36 g12; C4 (Z_to_bv 64 1); CB 4 g52; C8 (Z_to_bv 64 0); CB 16 g64;
                           C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); CB 4 g92a; C8 (Z_to_bv 64 wnd); CB 8 g104a;
                           C8 (Z_to_bv 64 prv); C8 (Z_to_bv 64 hd); CB 4 g128;
                           C4 (Z_to_bv 64 32768); C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 32767); C4 (Z_to_bv 64 5); CB 12 g148]) ->
     rw_cells psegs M1 (s + 5888) [CB 8 j3a; C4 (Z_to_bv 64 16384); CB 52 j3b; C8 (Z_to_bv 64 0); CB 8 j3c] ->
     Q (MS (mkR (Z_to_bv 64 0x16620) (Z_to_bv 64 (usp + -288)) x3 x4 x5 x6 x7
                (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 s) (Z_to_bv 64 65536) (Z_to_bv 64 16384) (Z_to_bv 64 4) (Z_to_bv 64 0x1a9f4) x14
                x15 x16 x17
                (Z_to_bv 64 (s + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x23abc) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR (Z_to_bv 64 0x165fc) (Z_to_bv 64 (usp + -288)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 s) (Z_to_bv 64 hd)
                       x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (s + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 15) x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x165fc) fc None M (seg_rom psegs)).
Proof.
  intros Q n cp up s wnd prv hd M F fc p0 p96 g12 g52 g64 g92a g104a g120 g148 j3 v19 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31
         NR CP UP WR PR HR S0 SHI TD B1 B3 MI HK.
  change (2^20) with 1048576 in NR. change (2^64) with 18446744073709551616 in CP, UP, WR, PR, HR.
  pose proof (fl_cb_range n ltac:(lia)) as CBR. change (2^21) with 2097152 in CBR.
  pose proof (munch_refl [(s + 120, s + 128); (s + 5896, s + 5900); (s + 5952, s + 5960)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  unfold TFC in *.
  do 9 step. do 4 step.
  apply evt_done. eapply HK; eassumption.
Qed.

End SEG.
