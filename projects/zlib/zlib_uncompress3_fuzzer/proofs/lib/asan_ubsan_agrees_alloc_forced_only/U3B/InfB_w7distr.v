(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfAGlue_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import InfPure_w7d InfPure_w7h InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.


Lemma swrap32_submod_d : forall a b, -2147483648 <= a - b < 2147483648 ->
  bv_swrap 32 (a mod 18446744073709551616 - b mod 18446744073709551616) = a - b.
Proof.
  intros a b Hab. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cw_land15_op : forall c, 0 <= code_op c <= 15 -> Z.land c 15 = code_op c.
Proof.
  intros c H. unfold code_op in *. replace (Z.land c 15) with (Z.land (Z.land c 255) 15) by (rewrite <- Z.land_assoc; reflexivity).
  exact (small_land_lo (Z.land c 255) 4 H ltac:(lia)).
Qed.

Lemma shl32_shr29 : forall x, 0 <= x < 4294967296 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 29 = 8 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 29) with 536870912. Z.div_mod_to_equations. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (RNG : footprint) (POST : machine_state -> Prop).

  Lemma dist_drop2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x29 x30 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (c1 c2 A4 T6 H : Z),
    0 <= H < 18446744073709551616 -> 0 <= c1 < 4294967296 -> 0 <= c2 < 4294967296 -> 0 <= code_bits c1 <= 15 -> 0 <= A4 - T6 <= 64 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (code_bits c1)) x11 (Z_to_bv 64 c2) (Z_to_bv 64 (code_op c2)) (Z_to_bv 64 (A4 - T6)) x15 x16 x17 x18 x19 x21 x25 x22 (Z_to_bv 64 (H / 2 ^ code_bits c1)) x20 x23 x26 x27 (Z_to_bv 64 (Z.shiftr c1 8)) x29 x30 (Z_to_bv 64 T6)) FR (Z_to_bv 64 0x92114) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 c2) x13 (Z_to_bv 64 A4) x15 x16 x17 x18 x19 x21 x25 x22 (Z_to_bv 64 H) x20 x23 x26 x27 (Z_to_bv 64 (Z.shiftr c1 8)) x29 x30 (Z_to_bv 64 T6)) FR (Z_to_bv 64 0x92104) fc None m (seg_rom bsegs)).
  Proof.
    intros until H. intros HH C1R C2R RB AS K.
    pose proof (cw_land31 c1 RB) as L31. pose proof (cw_shr8_range c1 C1R) as S8R.
    zs. rewrite (swrap32_submod_d A4 T6) by lia.
    zs. rewrite ?(Z.mod_small (Z.shiftr c1 8)) by lia. rewrite L31.
    zs. rewrite ?(Z.mod_small c2 18446744073709551616) by lia. change (Z.land c2 255) with (code_op c2).
    zs. rewrite (srl_div H (code_bits c1)) by lia.
    exact K.
  Time Qed.

  Lemma dist_join1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (c : Z),
    0 <= c < 4294967296 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (Z.shiftl (code_val c) 16)) x11 (Z_to_bv 64 c) x13 x14 x15 x16 x17 x18 x19 x21 x25 x22 x24 x20 x23 x26 x27 (Z_to_bv 64 (Z.shiftr c 8)) (Z_to_bv 64 (code_bits c)) x30 x31) FR (Z_to_bv 64 0x91e80) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (code_val c)) x11 (Z_to_bv 64 (Z.land c 65535)) x13 x14 x15 x16 x17 x18 x19 x21 x25 x22 x24 x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x91e70) fc None m (seg_rom bsegs)).
  Proof.
    intros until c. intros CR K.
    pose proof (code_val_range c) as VALR. pose proof (cw_shr8_range c CR) as S8R.
    assert (LO : 0 <= Z.land c 65535 < 65536) by (change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    assert (SH : 0 <= Z.shiftl (code_val c) 16 < 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 16) with 65536; lia).
    zs. zs. rewrite ?(Z.mod_small (Z.shiftl (code_val c) 16)) by lia.
    rewrite (code_word_join c CR).
    zs. zs. change (Z.land (Z.shiftr c 8) 255) with (code_bits c).
    exact K.
  Time Qed.

  Lemma dist_join2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (c rb : Z),
    0 <= c < 4294967296 -> 1 <= rb <= 15 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (code_bits c + rb)) x11 (Z_to_bv 64 c) x13 x14 x15 x16 x17 x18 x19 x21 x25 x22 x24 x20 (Z_to_bv 64 (code_bits c)) (Z_to_bv 64 (Z.shiftr c 8)) x27 x28 (Z_to_bv 64 rb) x30 x31) FR (Z_to_bv 64 0x91ff8) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (code_val c)) x11 (Z_to_bv 64 (Z.land c 65535)) x13 x14 x15 x16 x17 x18 x19 x21 x25 x22 x24 x20 x23 x26 x27 x28 (Z_to_bv 64 rb) x30 x31) FR (Z_to_bv 64 0x91fe4) fc None m (seg_rom bsegs)).
  Proof.
    intros until rb. intros CR RB K.
    pose proof (code_val_range c) as VALR. pose proof (cw_shr8_range c CR) as S8R.
    assert (LO : 0 <= Z.land c 65535 < 65536) by (change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    assert (SH : 0 <= Z.shiftl (code_val c) 16 < 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 16) with 65536; lia).
    zs. zs. rewrite ?(Z.mod_small (Z.shiftl (code_val c) 16)) by lia.
    rewrite (code_word_join c CR).
    zs. zs. zs. change (Z.land (Z.shiftr c 8) 255) with (code_bits c).
    exact K.
  Time Qed.

  Lemma dist_six_b1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x25 x26 x27 x28 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (rb op H B bz : Z),
    0 <= B <= 40 -> 0 <= H < 2 ^ B -> 0 <= bz < 256 -> 1 <= rb <= 15 -> 1 <= op -> rb + op <= 15 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 ((H + bz * 2 ^ B) mod 2 ^ (rb + op) / 2 ^ rb)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (2 ^ (rb + op) - 1)) x25 (Z_to_bv 64 B) (Z_to_bv 64 (H + bz * 2 ^ B)) x20 x23 x26 x27 x28 (Z_to_bv 64 rb) x30 x31) FR (Z_to_bv 64 0x92048) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 bz) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (2 ^ (rb + op) - 1)) x25 (Z_to_bv 64 B) (Z_to_bv 64 H) x20 x23 x26 x27 x28 (Z_to_bv 64 rb) x30 x31) FR (Z_to_bv 64 0x92038) fc None m (seg_rom bsegs)).
  Proof.
    intros until bz. intros BR HH BZ RB OP1 OP15 K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    pose proof (pull_bound H B bz ltac:(lia) ltac:(lia) BZ) as PB.
    pose proof (Z.pow_le_mono_r 2 (B + 8) 48 ltac:(lia) ltac:(lia)) as P48. change (2 ^ 48) with 281474976710656 in P48.
    zs. zs.
    rewrite (pull_hold H bz B) by lia.
    remember (H + bz * 2 ^ B) as H1 eqn:EH1.
    pose proof (pow2_le_15 (rb + op) ltac:(lia)) as P15. pose proof (pow2_le_15 rb ltac:(lia)) as PRB. pose proof (pow2_le_15 op ltac:(lia)) as POP.
    pose proof (mod_pow2_bound H1 (rb + op) ltac:(lia)) as MR. pose proof (sidx_range rb op H1 ltac:(lia) ltac:(lia)) as JR.
    zs. rewrite (InfAGlue_w7.land_mask_mod H1 (rb + op)) by lia.
    zs. rewrite (srlw_wrap_small (H1 mod 2 ^ (rb + op)) rb) by lia.
    exact K.
  Time Qed.

  Lemma dist_six_b2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA J val : Z),
    0 <= J < 65536 -> 0 <= val < 65536 -> 0 < TA < 140737488355328 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (J + val)) (Z_to_bv 64 (4 * (J + val) + TA)) x12 (Z_to_bv 64 (Z.shiftl (J + val) 32)) x14 (Z_to_bv 64 TA) x16 x17 x18 x19 x21 x25 x22 x24 x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x92064) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 J) (Z_to_bv 64 val) x12 x13 x14 (Z_to_bv 64 TA) x16 x17 x18 x19 x21 x25 x22 x24 x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x9204c) fc None m (seg_rom bsegs)).
  Proof.
    intros until val. intros JR VAL TAR K.
    zs. zs. zs. rewrite (zext32_shift30 (J + val)) by lia.
    zrung [0x92064].
    exact K.
  Time Qed.

  Lemma dist_six_c : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x14 x15 x17 x18 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA idx B T6 HV NX1 : Z),
    0 <= B <= 64 -> 0 <= idx < 4294967296 -> 0 < TA < 140737488355328 -> 1 <= HV < 67108864 -> 0 < NX1 < 140737488355328 -> -64 <= T6 <= 64 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 1) (Z_to_bv 64 NX1) (Z_to_bv 64 NX1) (Z_to_bv 64 idx) x14 x15 (Z_to_bv 64 1) x17 x18 (Z_to_bv 64 (HV + -1)) x21 x25 (Z_to_bv 64 (B + 8)) x24 x20 x23 x26 x27 x28 x29 x30 (Z_to_bv 64 (T6 + -8))) FR (Z_to_bv 64 0x91fb0) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (4 * idx + TA)) (Z_to_bv 64 NX1) (Z_to_bv 64 (Z.shiftl idx 32)) x14 x15 (Z_to_bv 64 1) x17 x18 (Z_to_bv 64 HV) x21 x25 (Z_to_bv 64 B) x24 x20 x23 x26 x27 x28 x29 x30 (Z_to_bv 64 T6)) FR (Z_to_bv 64 0x92070) fc None m (seg_rom bsegs)).
  Proof.
    intros until NX1. intros BR IR TAR HVR NXR T6R K.
    zrung [0x91fb0].
    rewrite ?(Z.mod_small idx) by lia.
    exact K.
  Time Qed.

  Lemma dist_ck2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A sb : Z),
    0 <= A < 140737488355328 -> (sb = 0 \/ (0 < sb <= 7 /\ A mod 8 + 1 - 1 < sb)) ->
    (forall y : word, evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y (Z_to_bv 64 A) x12 (Z_to_bv 64 sb) x14 x15 x16 x17 x18 x19 x21 x25 x22 x24 x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x92030) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 (Z_to_bv 64 sb) x14 x15 x16 x17 x18 x19 x21 x25 x22 x24 x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x9202c) fc None m (seg_rom bsegs)).
  Proof.
    intros until sb. intros AR CK K.
    ck_branchJ 10 0x92030 CK.
    apply K.
  Time Qed.

  Lemma dist_six_a1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (c1 H : Z),
    0 <= H < 18446744073709551616 -> 0 <= c1 < 4294967296 -> 1 <= code_bits c1 <= 15 -> 1 <= code_op c1 -> code_bits c1 + code_op c1 <= 15 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (H mod 2 ^ (code_bits c1 + code_op c1) / 2 ^ code_bits c1)) x11 (Z_to_bv 64 (code_val c1)) (Z_to_bv 64 (code_bits c1 + code_op c1)) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (2 ^ (code_bits c1 + code_op c1) - 1)) x25 x22 (Z_to_bv 64 H) x20 x23 x26 x27 x28 (Z_to_bv 64 (code_bits c1)) x30 x31) FR (Z_to_bv 64 0x91f70) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 c1) x13 x14 x15 x16 x17 x18 x19 x21 x25 x22 (Z_to_bv 64 H) x20 x23 x26 x27 x28 (Z_to_bv 64 (code_bits c1)) x30 x31) FR (Z_to_bv 64 0x91f34) fc None m (seg_rom bsegs)).
  Proof.
    intros until H. intros HH C1R RB OP1 OP15 K.
    pose proof (cw_landE000 c1 ltac:(lia)) as LE0. pose proof (code_val_range c1) as VALR.
    pose proof (cw_land15_op c1 ltac:(lia)) as L15.
    set (rb := code_bits c1) in *. set (op := code_op c1) in *.
    pose proof (pow2_le_15 (rb + op) ltac:(lia)) as P15. pose proof (pow2_le_15 rb ltac:(lia)) as PRB. pose proof (pow2_le_15 op ltac:(lia)) as POP.
    pose proof (mod_pow2_bound H (rb + op) ltac:(lia)) as MR. pose proof (sidx_range rb op H ltac:(lia) ltac:(lia)) as JR.
    zs. zs. rewrite ?(Z.mod_small c1 18446744073709551616) by lia. rewrite LE0.
    zrung [0x91f44].
    zs. rewrite ?(Z.mod_small c1 18446744073709551616) by lia. rewrite L15.
    zrung [0x91f58].
    zs. rewrite (code_word_val c1 C1R). set (val := code_val c1) in *.
    zs. zs. zs.
    rewrite (mask_sllw (rb + op)) by lia.
    zs. rewrite (InfAGlue_w7.land_mask_mod H (rb + op)) by lia.
    zs. rewrite (srlw_wrap_small (H mod 2 ^ (rb + op)) rb) by lia.
    exact K.
  Time Qed.

  Lemma dist_six_a2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA J val rb B : Z),
    0 <= J < 65536 -> 0 <= val < 65536 -> 0 < TA < 140737488355328 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (4 * (J + val) + TA)) (Z_to_bv 64 (J + val)) x14 (Z_to_bv 64 TA) (Z_to_bv 64 1) (Z_to_bv 64 B) x18 x19 x21 x25 (Z_to_bv 64 B) x24 x20 x23 x26 x27 x28 (Z_to_bv 64 rb) x30 (Z_to_bv 64 rb)) FR (Z_to_bv 64 0x91fa8) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 J) x11 (Z_to_bv 64 val) x13 x14 (Z_to_bv 64 TA) (Z_to_bv 64 1) (Z_to_bv 64 B) x18 x19 x21 x25 x22 x24 x20 x23 x26 x27 x28 (Z_to_bv 64 rb) x30 x31) FR (Z_to_bv 64 0x91f74) fc None m (seg_rom bsegs)).
  Proof.
    intros until B. intros JR VAL TAR K.
    zs. zs. zs. rewrite (zext32_shift30 (J + val)) by lia.
    zrung [0x91fa8].
    rewrite ?(Z.mod_small (J + val)) by lia.
    exact K.
  Time Qed.

  Lemma dist_root_a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x16 x17 x18 x19 x20 x23 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA db H B0 HV0 : Z),
    0 <= H < 18446744073709551616 -> 1 <= db <= 15 -> 0 < TA < 140737488355328 -> 0 <= B0 <= 40 -> 0 <= HV0 < 67108864 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 HV0) (Z_to_bv 64 (8 * HV0)) x7 x8 x9 (Z_to_bv 64 (Z.shiftl B0 32)) (Z_to_bv 64 (4 * (H mod 2 ^ db) + TA)) (Z_to_bv 64 (H mod 2 ^ db)) x13 (Z_to_bv 64 B0) (Z_to_bv 64 TA) (Z_to_bv 64 1) (Z_to_bv 64 B0) x18 (Z_to_bv 64 (Z.shiftl HV0 32)) (Z_to_bv 64 HV0) x25 (Z_to_bv 64 B0) (Z_to_bv 64 H) x20 x23 x26 x27 x28 x29 (Z_to_bv 64 HV0) (Z_to_bv 64 (2 ^ db - 1))) FR (Z_to_bv 64 0x91e34) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 db) x12 x13 x14 (Z_to_bv 64 TA) x16 x17 x18 x19 (Z_to_bv 64 HV0) x25 (Z_to_bv 64 B0) (Z_to_bv 64 H) x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x91dd8) fc None m (seg_rom bsegs)).
  Proof.
    intros until HV0. intros HH DB TAR B0R HVR K.
    pose proof (pow2_le_15 db ltac:(lia)) as P15. pose proof (mod_pow2_bound H db ltac:(lia)) as MR.
    zs. zrung [0x91de4].
    zs. zs. zs.
    rewrite (mask_sllw db) by lia.
    zs. rewrite (root_idx H db) by lia.
    zs. rewrite shl2.
    zs.
    zrung [0x91e18].
    zs. zs. zs. zs. zs. zs. zs.
    rewrite (Z.mod_small HV0 4294967296) by lia. rewrite (Z.mod_small B0 4294967296) by lia. rewrite (shl32_shr29 HV0) by lia.
    exact K.
  Time Qed.

  Lemma dist_root_b : forall (x1 x2 x3 x4 x8 x9 x11 x12 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA db H B bz NX A4 T1 T0 HV : Z),
    0 <= B <= 40 -> 0 <= H < 2 ^ B -> 0 <= bz < 256 -> 1 <= db <= 15 -> 0 < TA < 140737488355328 -> 0 < NX < 140737488355328 -> 0 <= A4 <= 40 -> 1 <= HV < 67108864 -> 1 <= T0 < 67108864 -> 8 <= T1 < 536870912 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 (T0 + -1)) (Z_to_bv 64 (T1 + -8)) (Z_to_bv 64 (NX + 1)) x8 x9 (Z_to_bv 64 1) (Z_to_bv 64 (NX + 1)) (Z_to_bv 64 ((H + bz * 2 ^ B) mod 2 ^ db)) (Z_to_bv 64 (NX + 1)) (Z_to_bv 64 (A4 + 8)) (Z_to_bv 64 TA) (Z_to_bv 64 1) (Z_to_bv 64 (B + 8)) x18 x19 x21 x25 x22 (Z_to_bv 64 (H + bz * 2 ^ B)) x20 x23 x26 x27 x28 x29 (Z_to_bv 64 (HV + -1)) (Z_to_bv 64 (2 ^ db - 1))) FR (Z_to_bv 64 0x91e3c) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 T0) (Z_to_bv 64 T1) (Z_to_bv 64 NX) x8 x9 (Z_to_bv 64 bz) x11 x12 (Z_to_bv 64 (NX + 1)) (Z_to_bv 64 A4) (Z_to_bv 64 TA) (Z_to_bv 64 1) (Z_to_bv 64 B) x18 x19 x21 x25 x22 (Z_to_bv 64 H) x20 x23 x26 x27 x28 x29 (Z_to_bv 64 HV) (Z_to_bv 64 (2 ^ db - 1))) FR (Z_to_bv 64 0x91ebc) fc None m (seg_rom bsegs)).
  Proof.
    intros until HV. intros BR HH BZ DB TAR NXR A4R HVR T0R T1R K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    pose proof (pull_bound H B bz ltac:(lia) ltac:(lia) BZ) as PB.
    pose proof (Z.pow_le_mono_r 2 (B + 8) 48 ltac:(lia) ltac:(lia)) as P48. change (2 ^ 48) with 281474976710656 in P48.
    pose proof (pow2_le_15 db ltac:(lia)) as P15.
    zs. zs.
    rewrite (pull_hold H bz B) by lia.
    remember (H + bz * 2 ^ B) as H1 eqn:EH1.
    pose proof (mod_pow2_bound H1 db ltac:(lia)) as MR.
    zs. rewrite (root_idx H1 db) by lia.
    zs. rewrite shl2.
    zs.
    zrung [0x91e3c].
    exact K.
  Time Qed.

  Lemma dist_stub1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (HV0 : Z),
    0 <= HV0 < 67108864 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 HV0) (Z_to_bv 64 (8 * HV0)) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (Z.shiftl HV0 32)) (Z_to_bv 64 HV0) x25 x22 x24 x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x93668) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (Z.shiftl HV0 32)) (Z_to_bv 64 HV0) x25 x22 x24 x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x935e4) fc None m (seg_rom bsegs)).
  Proof.
    intros until HV0. intros HVR K.
    zs. zs. zs.
    rewrite (Z.mod_small HV0 4294967296) by lia. rewrite (Z.shiftl_mul_pow2 HV0 3) by lia. change (2 ^ 3) with 8. replace (HV0 * 8) with (8 * HV0) by lia.
    exact K.
  Time Qed.

  Lemma dist_ck1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A sb : Z),
    0 <= A < 140737488355328 -> (sb = 0 \/ (0 < sb <= 7 /\ A mod 8 + 1 - 1 < sb)) ->
    (forall y : word, evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y (Z_to_bv 64 A) (Z_to_bv 64 sb) x13 x14 x15 x16 x17 x18 x19 x21 x25 x22 x24 x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x91eb8) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) (Z_to_bv 64 sb) x13 x14 x15 x16 x17 x18 x19 x21 x25 x22 x24 x20 x23 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x91eb4) fc None m (seg_rom bsegs)).
  Proof.
    intros until sb. intros AR CK K.
    ck_branchJ 10 0x91eb8 CK.
    apply K.
  Time Qed.
End S.
End CANSEC1.
