(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Tac Image ZBridge Walk Arr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CkP Require Import RegsFull BridgeKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Plain Require Import PImg FlKit FlSeg1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Plain Require Import RunDraw.
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

Definition TSC (p12 p56 p88 : list byte) (up cp n : Z) : list cell :=
  [C8 (Z_to_bv 64 cp); C4 (Z_to_bv 64 2); CB 36 p12; C8 (Z_to_bv 64 0); CB 8 p56;
   C8 (Z_to_bv 64 0x19ff8); C8 (Z_to_bv 64 0x1a008); C8 (Z_to_bv 64 0); CB 24 p88;
   C8 (Z_to_bv 64 up); C8 (Z_to_bv 64 cp); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0x161c4)].
Definition TSSV (up cp n : Z) : list cell :=
  [C8 (Z_to_bv 64 up); C8 (Z_to_bv 64 cp); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0x161c4)].
Definition IIC (up n cl : Z) : list cell :=
  [C8 (Z_to_bv 64 up); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 cl); C8 (Z_to_bv 64 0x16004)].

Lemma fl_seg_ts1 : forall (Q : machine_state -> Prop) (n cp up cl lo : Z) (pad : list byte) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v18 v9 v8 v1 : word),
  lo <= usp + -288 -> 0 <= lo -> 4 <= n <= 2^20 -> 0 < cp < 2^64 -> 0 < up < 2^64 -> 0 <= cl < 2^64 ->
  stk psegs M lo (usp + -48) -> mem_inv psegs M -> relro_pristine M ->
  rw_cells psegs M (usp + -48) (LFC pad cl v18 v9 v8 v1) ->
  (forall (M1 : word -> option byte) (p12 p56 p88 : list byte),
     munch [(usp + -224, usp + -48)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -224) ->
     rw_cells psegs M1 (usp + -192) (TSC p12 p56 p88 up cp n) ->
     rw_cells psegs M1 (usp + -224) (IIC up n cl) ->
     rw_cells psegs M1 (usp + -48) (LFC pad cl v18 v9 v8 v1) ->
     Q (MS (mkR (Z_to_bv 64 0x1ce50) (Z_to_bv 64 (usp + -224)) x3 x4 x5 x6 x7
                (Z_to_bv 64 cl) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 7176) (Z_to_bv 64 1) (Z_to_bv 64 7176) (Z_to_bv 64 0x19ff8)
                (Z_to_bv 64 112) x15 x16 x17
                (Z_to_bv 64 up) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x20a98) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -48)) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 cp) x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 up) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x161b0) fc None M (seg_rom psegs)).
Proof.
  intros Q n cp up cl lo pad M F fc x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v18 v9 v8 v1
         LO LO0 NR CP UP CL ST MI RP LF HK.
  change (2^20) with 1048576 in NR. change (2^64) with 18446744073709551616 in CP, UP, CL.
  pose proof (munch_refl [(usp + -224, usp + -48)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  relro_cells RP. unfold LFC in LF. unfold TSC, IIC, LFC in HK.
  do 5 step.
  step. carve_frame 144%nat ST. replace (usp + -48 + -144) with (usp + -192) in * by lia.
  do 4 step. do 3 step. do 6 step. do 5 step.
  (* 1.4 inflateInit_ (0x1cd90): the version / stream_size / strm checks come before the prologue; msg := NULL;
     zalloc = NULL takes the default (zcalloc) and zfree = NULL the default (zcfree); then the prologue and the
     zalloc call; zcalloc tail-jumps to calloc *)
  do 2 step. if_false. do 2 step. if_false. do 3 step. if_false. step. br_false.
  do 3 step. if_true. do 6 step. if_false. do 4 step.
  step. carve_frame 32%nat ST. replace (usp + -192 + -32) with (usp + -224) in * by lia.
  do 4 step. do 6 step.
  do 4 step.
  apply evt_done. eapply HK; eassumption.
Qed.

Lemma fl_seg_i1 : forall (Q : machine_state -> Prop) (n up cl lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -288 -> 0 <= lo -> 4 <= n <= 2^20 -> 0 < up < 2^64 -> 0 <= cl < 2^64 ->
  stk psegs M lo (usp + -48) -> mem_inv psegs M ->
  (forall (M1 : word -> option byte),
     munch [(usp + -168, usp + -156)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -48) ->
     OP.rdn psegs M1 (Z_to_bv 64 (usp + -168)) 8 = Some (Z_to_le_bytes 8 up) ->
     OP.rdn psegs M1 (Z_to_bv 64 (usp + -160)) 4 = Some (Z_to_le_bytes 4 n) ->
     Q (MS (mkR (Z_to_bv 64 0x1601c) (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 (Z_to_bv 64 cl) (Z_to_bv 64 n)
                (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 up) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x1cf48) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 (Z_to_bv 64 cl) (Z_to_bv 64 n) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 up) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16004) fc None M (seg_rom psegs)).
Proof.
  intros Q n up cl lo M F fc x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 NR UP CL ST MI HK.
  change (2^20) with 1048576 in NR. change (2^64) with 18446744073709551616 in UP, CL.
  pose proof (munch_refl [(usp + -168, usp + -156)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  destruct (stk_split psegs M lo (usp + -156) (usp + -48) ST ltac:(lia)) as [STa STb].
  carve_frame 12%nat STa.
  step. if_false. do 2 step. do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (R1 : OP.rdn psegs m1 (Z_to_bv 64 (usp + -168)) 8 = Some (Z_to_le_bytes 8 up)) by (cell_fact FR 0%nat);
    assert (R2 : OP.rdn psegs m1 (Z_to_bv 64 (usp + -160)) 4 = Some (Z_to_le_bytes 4 n)) by (cell_fact FR 8%nat)
  end.
  release_frame FR STa (usp + -156).
  pose proof (stk_merge psegs _ _ _ _ STa STb ltac:(lia)) as ST'.
  apply evt_done. eapply HK; try eassumption.
Qed.

Lemma fl_seg_i2 : forall (Q : machine_state -> Prop) (n up cl lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -288 -> 0 <= lo -> 4 <= n <= 2^20 -> 0 < up < 2^64 -> 2 <= cl < 2^64 ->
  stk psegs M lo (usp + -48) -> mem_inv psegs M ->
  (forall (M1 : word -> option byte),
     munch [(usp + -184, usp + -180)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -48) ->
     OP.rdn psegs M1 (Z_to_bv 64 (usp + -184)) 4 = Some (Z_to_le_bytes 4 (cl - 2)) ->
     Q (MS (mkR (Z_to_bv 64 0x16030) (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 (Z_to_bv 64 (cl - 2)) (Z_to_bv 64 n)
                (Z_to_bv 64 (usp + -192)) x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 up) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x1eefc) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 (Z_to_bv 64 cl) (Z_to_bv 64 n) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 up) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x1601c) fc None M (seg_rom psegs)).
Proof.
  intros Q n up cl lo M F fc x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 NR UP CL ST MI HK.
  change (2^20) with 1048576 in NR. change (2^64) with 18446744073709551616 in UP, CL.
  pose proof (munch_refl [(usp + -184, usp + -180)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  destruct (stk_split psegs M lo (usp + -180) (usp + -48) ST ltac:(lia)) as [STa STb].
  carve_frame 4%nat STa.
  step. if_false. do 2 step. do 2 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (R1 : OP.rdn psegs m1 (Z_to_bv 64 (usp + -184)) 4 = Some (Z_to_le_bytes 4 (cl - 2))) by (cell_fact FR 0%nat)
  end.
  release_frame FR STa (usp + -180).
  pose proof (stk_merge psegs _ _ _ _ STa STb ltac:(lia)) as ST'.
  apply evt_done. eapply HK; try eassumption.
Qed.

Lemma fl_seg_iE1 : forall (Q : machine_state -> Prop) (e : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  -2^31 <= e < 2^31 -> e <> 0 ->
  mem_inv psegs M -> relro_pristine M ->
  Q (MS (mkR (Z_to_bv 64 0x160ec) (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 x8 x9
             (Z_to_bv 64 0x2a418) (Z_to_bv 64 0x102f2) (Z_to_bv 64 0x10570) (Z_to_bv 64 e) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x22750) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 e) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x1601c) fc None M (seg_rom psegs)).
Proof.
  intros Q e M F fc x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ER ENZ MI RP HK.
  change (2^31) with 2147483648 in ER.
  relro_cells RP.
  step. brw_true. do 9 step. step.
  apply evt_done. exact HK.
Qed.

Lemma fl_seg_i3 : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x16040) (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 x8 x9
             (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 4) x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1cf48) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16030) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  step. if_false. do 3 step. apply evt_done. exact HK.
Qed.

Lemma fl_seg_iE2 : forall (Q : machine_state -> Prop) (e : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  -2^31 <= e < 2^31 -> e <> 0 ->
  mem_inv psegs M -> relro_pristine M ->
  Q (MS (mkR (Z_to_bv 64 0x160ec) (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 x8 x9
             (Z_to_bv 64 0x2a418) (Z_to_bv 64 0x102f2) (Z_to_bv 64 0x103f9) (Z_to_bv 64 e) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x22750) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 e) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16030) fc None M (seg_rom psegs)).
Proof.
  intros Q e M F fc x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ER ENZ MI RP HK.
  change (2^31) with 2147483648 in ER.
  relro_cells RP.
  step. brw_true. do 8 step. step.
  apply evt_done. exact HK.
Qed.

Lemma fl_seg_zw : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x1ed54) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 32768) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 0x19ff8) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x20a98) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 0x19ff8) x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x1ed50) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 5 step. apply evt_done. exact HK.
Qed.

Ltac ie_check md :=
  do 3 step; br_false; do 2 step; if_false; do 2 step; if_false; do 2 step; br_false; do 2 step; br_true;
  do 5 step; step;
  replace (bv_unsigned (sx32 (Z_to_bv 64 md))) with md in *;
  [ | unfold sx32; rewrite (unsigned_lit md) by lia; rewrite bv_swrap_small;
      [ rewrite unsigned_lit by lia; reflexivity | change (bv_half_modulus 32) with 2147483648%Z; lia ] ];
  replace (bv_swrap 32 (md + 18446744073709535436)) with (md - 16180) in *;
  [ | unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with 2147483648%Z; change (bv_modulus 32) with 4294967296%Z; lia ];
  brw_false.

Lemma fl_seg_i4w : forall (Q : machine_state -> Prop) (p w md rc3 s0v lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -288 -> 0 <= lo -> 0 < p -> p + 7176 <= lo -> 0 < w < 2^64 -> 16180 <= md <= 16211 ->
  (rc3 = -3 \/ rc3 = 1) -> 0 <= s0v < 2^64 ->
  stk psegs M lo (usp + -48) -> mem_inv psegs M ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -136)) 8 = Some (Z_to_le_bytes 8 p) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -128)) 8 = Some (Z_to_le_bytes 8 0x19ff8) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -120)) 8 = Some (Z_to_le_bytes 8 0x1a008) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -112)) 8 = Some (Z_to_le_bytes 8 0) ->
  OP.rdn psegs M (Z_to_bv 64 p) 8 = Some (Z_to_le_bytes 8 (usp + -192)) ->
  OP.rdn psegs M (Z_to_bv 64 (p + 8)) 4 = Some (Z_to_le_bytes 4 md) ->
  OP.rdn psegs M (Z_to_bv 64 (p + 88)) 8 = Some (Z_to_le_bytes 8 w) ->
  (forall (M1 : word -> option byte) (y13 y15 : word),
     munch [(usp + -208, usp + -192)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -208) ->
     rw_cells psegs M1 (usp + -208) [C8 (Z_to_bv 64 s0v); C8 (Z_to_bv 64 0x16058)] ->
     Q (MS (mkR (Z_to_bv 64 0x1eecc) (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -192)) x9
                (Z_to_bv 64 w) (Z_to_bv 64 w) (Z_to_bv 64 (usp + -192)) y13 (Z_to_bv 64 0x1a008) y15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x20958) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 (Z_to_bv 64 s0v) x9 (Z_to_bv 64 rc3) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16040) fc None M (seg_rom psegs)).
Proof.
  intros Q p w md rc3 s0v lo M F fc x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 P0 PHI WR MD RC S0V ST MI R1 R2 R3 R4 R5 R6 R7 HK.
  change (2^64) with 18446744073709551616 in WR, S0V.
  pose proof (munch_refl [(usp + -208, usp + -192)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  pose proof (ro_C8_of_rdn_Z M _ _ R1 ltac:(lia) ltac:(lia) ltac:(lia)) as RC1.
  pose proof (ro_C8_of_rdn_Z M _ _ R2 ltac:(lia) ltac:(lia) ltac:(lia)) as RC2.
  pose proof (ro_C8_of_rdn_Z M _ _ R3 ltac:(lia) ltac:(lia) ltac:(lia)) as RC3.
  pose proof (ro_C8_of_rdn_Z M _ _ R4 ltac:(lia) ltac:(lia) ltac:(lia)) as RC4.
  pose proof (ro_C8_of_rdn_Z M _ _ R5 ltac:(lia) ltac:(lia) ltac:(lia)) as RC5.
  pose proof (ro_C4_of_rdn_Z M _ _ R6 ltac:(lia) ltac:(lia) ltac:(lia)) as RC6.
  pose proof (ro_C8_of_rdn_Z M _ _ R7 ltac:(lia) ltac:(lia) ltac:(lia)) as RC7.
  clear R1 R2 R3 R4 R5 R6 R7.
  destruct (stk_split psegs M lo (usp + -192) (usp + -48) ST ltac:(lia)) as [STa STb].
  destruct RC as [-> | ->]; [ do 2 step; if_true; do 2 step | do 2 step; if_false; do 2 step; if_false; do 2 step ].
  all: ie_check md.
  all: step; carve_frame 16%nat STa; replace (usp + -192 + -16) with (usp + -208) in * by lia; do 2 step.
  all: do 2 step; br_false; do 3 step; step; do 2 step.
  all: apply evt_done; eapply HK; eassumption.
Qed.

Lemma fl_seg_i4n : forall (Q : machine_state -> Prop) (p md rc3 s0v lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -288 -> 0 <= lo -> 0 < p -> p + 7176 <= lo -> 16180 <= md <= 16211 ->
  (rc3 = -3 \/ rc3 = 1) -> 0 <= s0v < 2^64 ->
  stk psegs M lo (usp + -48) -> mem_inv psegs M ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -136)) 8 = Some (Z_to_le_bytes 8 p) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -128)) 8 = Some (Z_to_le_bytes 8 0x19ff8) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -120)) 8 = Some (Z_to_le_bytes 8 0x1a008) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -112)) 8 = Some (Z_to_le_bytes 8 0) ->
  OP.rdn psegs M (Z_to_bv 64 p) 8 = Some (Z_to_le_bytes 8 (usp + -192)) ->
  OP.rdn psegs M (Z_to_bv 64 (p + 8)) 4 = Some (Z_to_le_bytes 4 md) ->
  OP.rdn psegs M (Z_to_bv 64 (p + 88)) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall (M1 : word -> option byte) (y13 y15 : word),
     munch [(usp + -208, usp + -192)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -208) ->
     rw_cells psegs M1 (usp + -208) [C8 (Z_to_bv 64 s0v); C8 (Z_to_bv 64 0x16058)] ->
     Q (MS (mkR (Z_to_bv 64 0x1eee4) (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -192)) x9
                (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 (usp + -192)) y13 (Z_to_bv 64 0x1a008) y15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x20958) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 (Z_to_bv 64 s0v) x9 (Z_to_bv 64 rc3) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16040) fc None M (seg_rom psegs)).
Proof.
  intros Q p md rc3 s0v lo M F fc x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 P0 PHI MD RC S0V ST MI R1 R2 R3 R4 R5 R6 R7 HK.
  change (2^64) with 18446744073709551616 in S0V.
  pose proof (munch_refl [(usp + -208, usp + -192)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  pose proof (ro_C8_of_rdn_Z M _ _ R1 ltac:(lia) ltac:(lia) ltac:(lia)) as RC1.
  pose proof (ro_C8_of_rdn_Z M _ _ R2 ltac:(lia) ltac:(lia) ltac:(lia)) as RC2.
  pose proof (ro_C8_of_rdn_Z M _ _ R3 ltac:(lia) ltac:(lia) ltac:(lia)) as RC3.
  pose proof (ro_C8_of_rdn_Z M _ _ R4 ltac:(lia) ltac:(lia) ltac:(lia)) as RC4.
  pose proof (ro_C8_of_rdn_Z M _ _ R5 ltac:(lia) ltac:(lia) ltac:(lia)) as RC5.
  pose proof (ro_C4_of_rdn_Z M _ _ R6 ltac:(lia) ltac:(lia) ltac:(lia)) as RC6.
  pose proof (ro_C8_of_rdn_Z M _ _ R7 ltac:(lia) ltac:(lia) ltac:(lia)) as RC7.
  clear R1 R2 R3 R4 R5 R6 R7.
  destruct (stk_split psegs M lo (usp + -192) (usp + -48) ST ltac:(lia)) as [STa STb].
  destruct RC as [-> | ->]; [ do 2 step; if_true; do 2 step | do 2 step; if_false; do 2 step; if_false; do 2 step ].
  all: ie_check md.
  all: step; carve_frame 16%nat STa; replace (usp + -192 + -16) with (usp + -208) in * by lia; do 2 step.
  all: do 2 step; if_true; do 2 step; step; do 2 step.
  all: apply evt_done; eapply HK; eassumption.
Qed.

Lemma fl_seg_ze1b : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (p : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= p < 2^64 ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -136)) 8 = Some (Z_to_le_bytes 8 p) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -120)) 8 = Some (Z_to_le_bytes 8 0x1a008) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -112)) 8 = Some (Z_to_le_bytes 8 0) ->
  Q (MS (mkR (Z_to_bv 64 0x1eee4) x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -192)) x9 (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 (usp + -192)) x13
             (Z_to_bv 64 0x1a008) x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x20958) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -192)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x1eecc) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc p x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         PR R1 R2 R3 HK.
  change (2^64) with 18446744073709551616 in PR.
  pose proof (ovr_of_rdn_Z M _ (usp + -192 + 56) _ R1 ltac:(lia) ltac:(lia)) as HR1.
  pose proof (ovr_of_rdn_Z M _ (usp + -192 + 72) _ R2 ltac:(lia) ltac:(lia)) as HR2.
  pose proof (ovr_of_rdn_Z M _ (usp + -192 + 80) _ R3 ltac:(lia) ltac:(lia)) as HR3.
  do 5 step. step. do 2 step. apply evt_done. exact HK.
Qed.

Lemma fl_seg_ic : forall (Q : machine_state -> Prop) (n cp up s0v lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -288 -> 0 <= lo -> 4 <= n <= 2^20 -> 0 < cp < 2^64 -> 0 < up < 2^64 -> 0 <= s0v < 2^64 ->
  stk psegs M lo (usp + -48) -> mem_inv psegs M ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -208)) 8 = Some (Z_to_le_bytes 8 s0v) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -200)) 8 = Some (Z_to_le_bytes 8 0x16058) ->
  rw_cells psegs M (usp + -80) (TSSV up cp n) ->
  (forall (M1 : word -> option byte),
     munch [(usp + -136, usp + -128)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -48) ->
     OP.rdn psegs M1 (Z_to_bv 64 (usp + -136)) 8 = Some (Z_to_le_bytes 8 0) ->
     rw_cells psegs M1 (usp + -80) (TSSV up cp n) ->
     Q (MS (mkR (Z_to_bv 64 0x161c4) (Z_to_bv 64 (usp + -48)) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 cp)
                (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 up) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x161c4) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -192)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x1eee4) fc None M (seg_rom psegs)).
Proof.
  intros Q n cp up s0v lo M F fc x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 NR CP UP S0V ST MI R1 R2 SA HK.
  change (2^20) with 1048576 in NR. change (2^64) with 18446744073709551616 in CP, UP, S0V.
  pose proof (munch_refl [(usp + -136, usp + -128)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  pose proof (ro_C8_of_rdn_Z M _ _ R1 ltac:(lia) ltac:(lia) ltac:(lia)) as RC1.
  pose proof (ro_C8_of_rdn_Z M _ _ R2 ltac:(lia) ltac:(lia) ltac:(lia)) as RC2.
  clear R1 R2. unfold TSSV in *.
  destruct (stk_split psegs M lo (usp + -128) (usp + -48) ST ltac:(lia)) as [STa STb].
  carve_frame 8%nat STa.
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (RZ : OP.rdn psegs m1 (Z_to_bv 64 (usp + -136)) 8 = Some (Z_to_le_bytes 8 0)) by (cell_fact FR 0%nat)
  end.
  release_frame FR STa (usp + -128).
  pose proof (stk_merge psegs _ _ _ _ STa STb ltac:(lia)) as ST'.
  do 4 step. step. if_true. do 5 step. do 2 step.
  apply evt_done. eapply HK; eassumption.
Qed.

Lemma fl_seg_iB : forall (Q : machine_state -> Prop) (rc3 : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  -2^31 <= rc3 < 2^31 -> rc3 <> -3 -> rc3 <> 1 ->
  mem_inv psegs M -> relro_pristine M ->
  Q (MS (mkR (Z_to_bv 64 0x16128) (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 x8 x9
             (Z_to_bv 64 0x1061a) (Z_to_bv 64 49) (Z_to_bv 64 1) (Z_to_bv 64 0x2a418) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x228ec) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 rc3) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16040) fc None M (seg_rom psegs)).
Proof.
  intros Q rc3 M F fc x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         RR RA RB MI RP HK.
  change (2^31) with 2147483648 in RR.
  relro_cells RP.
  do 2 step. brw_false. do 2 step. brw_true.
  do 8 step.
  apply evt_done. exact HK.
Qed.

Lemma fl_seg_ts_ret : forall (pc0 : Z), pc0 = 0x160ec \/ pc0 = 0x16128 ->
  forall (Q : machine_state -> Prop) (n cp up : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  4 <= n <= 2^20 -> 0 < cp < 2^64 -> 0 < up < 2^64 ->
  rw_cells psegs M (usp + -80) (TSSV up cp n) -> mem_inv psegs M ->
  Q (MS (mkR (Z_to_bv 64 0x161c4) (Z_to_bv 64 (usp + -48)) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 cp) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 up) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x161c4) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -192)) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 pc0) fc None M (seg_rom psegs)).
Proof.
  intros pc0 HPC Q n cp up M F fc x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         NR CP UP SA MI HK.
  change (2^20) with 1048576 in NR. change (2^64) with 18446744073709551616 in CP, UP.
  unfold TSSV in SA.
  destruct HPC as [-> | ->]; [| step]; (do 7 step; apply evt_done; exact HK).
Qed.

Lemma fl_seg_fin1 : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x161cc) x2 x3 x4 x5 x6 x7 x8 x9 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x20958) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x161c4) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 2 step. apply evt_done. exact HK.
Qed.

Lemma fl_seg_fin2 : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x161d4) x2 x3 x4 x5 x6 x7 x8 x9 x18 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x20958) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x161cc) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 2 step. apply evt_done. exact HK.
Qed.

Lemma fl_seg_ret : forall (Q : machine_state -> Prop) (lo cl : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (pad : list byte)
    (ra v8 v9 v18 x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 <= lo <= usp + -48 ->
  stk psegs M lo (usp + -48) ->
  rw_cells psegs M (usp + -48) (LFC pad cl v18 v9 v8 ra) ->
  (stk psegs M lo usp ->
   Q (MS (mkR ra (Z_to_bv 64 usp) x3 x4 x5 x6 x7 v8 v9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 v18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (ret_pc ra) fc None M (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -48)) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x161d4) fc None M (seg_rom psegs)).
Proof.
  intros Q lo cl M F fc pad ra v8 v9 v18 x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO ST FR HK.
  unfold LFC in FR.
  do 5 step. step. release_frame FR ST usp. step. apply evt_done. replace (usp + -48 + 48) with usp by lia. exact (HK ST).
Qed.

End SEG.
