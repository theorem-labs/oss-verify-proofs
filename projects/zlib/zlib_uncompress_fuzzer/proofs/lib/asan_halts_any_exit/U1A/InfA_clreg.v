(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_w7d InfAGlue_w7 InfPure_table.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab InfA_w7pull InfA_w6kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint_hyp := lazymatch goal with |- acc_in ?R ?x => match goal with HA : acc_in R x |- _ => exact HA end end.
Local Ltac acc_hint ::= first [ acc_hint_hyp | acc_hint_sh ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Lemma zext32_shift31 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 31 = 2 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Lemma land_ones_mod : forall x k, 0 <= k -> Z.land x (2 ^ k - 1) = x mod 2 ^ k.
Proof. intros x k Hk. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. exact Hk. Qed.

(* the codelens snippets restated against the 1.4 listing (t1/dis/unc14.dis).
   - 1.4 keeps hold in s4 (x20) and the input count in s11 (x27); 1.3.1 had s10 (x26) and s8 (x24).
   - 1.4 keeps next_in in frame slot 496 and lens in slot 400, so cl_mask, cl_fill_a and the pull steps stop before a frame
     access, which the caller steps with its own memory facts.
   - cl_dec_adv, cl_x17, cl_x18 and cl_padv16/17/18 sit at their 1.4 pcs: the decode loop tail 0x8f260, the 17 / 18 tails
     0x8f464 / 0x8f4e0, and the repeat-16 / 17 / 18 pull bodies 0x8f3c0 / 0x8f358 / 0x8f428. *)
Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (RNG : footprint) (POST : machine_state -> Prop).

  (* 0x8f1bc li a3,-1; sllw a1,a3,a1; not t0,a1; mv t2,s11 *)
  Lemma cl_mask : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lb : Z),
    1 <= lb <= 15 ->
    (forall (x11' x13' : word), evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 (2 ^ lb - 1)) x6 x27 x8 x9 x10 x11' x12 x13' x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f21c) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 lb) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f20c) fc None m (seg_rom asegs)).
  Proof.
    intros until lb. intros LB K.
    zs. zs. zs.
    rewrite (mask_sllw lb) by lia.
    zs.
    apply K.
  Qed.

  (* 0x8f1d0 and t4,t0,s4; sll a1,t4,2; add a1,a6,a1; add a1,a1,1 *)
  Lemma cl_idx_a : forall (x1 x2 x3 x4 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA lb H : Z),
    0 <= H < 18446744073709551616 -> 1 <= lb <= 15 -> 0 <= TA < 140737488355328 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 (2 ^ lb - 1)) x6 x7 x8 x9 x10 (Z_to_bv 64 (TA + 4 * (H mod 2 ^ lb) + 1)) x12 x13 x14 x15 (Z_to_bv 64 TA) x17 x18 x19 (Z_to_bv 64 H) x21 x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 (H mod 2 ^ lb)) x30 x31) FR (Z_to_bv 64 0x8f230) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 (2 ^ lb - 1)) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 TA) x17 x18 x19 (Z_to_bv 64 H) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f220) fc None m (seg_rom asegs)).
  Proof.
    intros until H. intros HH LB TAR K.
    pose proof (pow2_le_15 lb ltac:(lia)) as P15. pose proof (mod_pow2_bound H lb ltac:(lia)) as MR.
    zs. rewrite (root_idx H lb) by lia.
    zs. rewrite shl2.
    zs. zs.
    exact K.
  Qed.

  (* 0x8f2a8 sll t4,t4,2; add a1,a6,t4; add a1,a1,2 *)
  Lemma cl_vaddr : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA i : Z),
    0 <= i < 32768 -> 0 <= TA < 140737488355328 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (TA + 4 * i + 2)) x12 x13 x14 x15 (Z_to_bv 64 TA) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 (4 * i)) x30 x31) FR (Z_to_bv 64 0x8f304) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 TA) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 i) x30 x31) FR (Z_to_bv 64 0x8f2f8) fc None m (seg_rom asegs)).
  Proof.
    intros until i. intros HI TAR K.
    zs. rewrite shl2.
    zs. zs.
    exact K.
  Qed.

  (* 0x8f22c sll a3,a3,t5; add s4,a3,s4; and t4,t0,s4; sll a3,t4,2; add a3,a6,a3; add a3,a3,1 *)
  Lemma cl_pull_idx : forall (x1 x2 x3 x4 x6 x7 x8 x9 x10 x11 x12 x14 x15 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA lb H B c : Z),
    0 <= c < 256 -> 0 <= B <= 40 -> 0 <= H < 2 ^ B -> 1 <= lb <= 15 -> 0 <= TA < 140737488355328 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 (2 ^ lb - 1)) x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (TA + 4 * ((H + c * 2 ^ B) mod 2 ^ lb) + 1)) x14 x15 (Z_to_bv 64 TA) x17 x18 x19 (Z_to_bv 64 (H + c * 2 ^ B)) x21 x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 ((H + c * 2 ^ B) mod 2 ^ lb)) (Z_to_bv 64 B) x31) FR (Z_to_bv 64 0x8f294) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 (2 ^ lb - 1)) x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 c) x14 x15 (Z_to_bv 64 TA) x17 x18 x19 (Z_to_bv 64 H) x21 x22 x23 x24 x25 x26 x27 x28 x29 (Z_to_bv 64 B) x31) FR (Z_to_bv 64 0x8f27c) fc None m (seg_rom asegs)).
  Proof.
    intros until c. intros HC HB HH LB TAR K.
    pose proof (pow2_le_15 lb ltac:(lia)) as P15. pose proof (pull_bound H B c ltac:(lia) HH HC) as PB. pose proof (pow2_48 (B + 8) ltac:(lia)) as P48.
    pose proof (mod_pow2_bound (H + c * 2 ^ B) lb ltac:(lia)) as MR.
    zs. zs. rewrite (pull_hold H c B) by lia.
    zs. rewrite (root_idx (H + c * 2 ^ B) lb) by lia.
    zs. rewrite shl2.
    zs. zs.
    exact K.
  Qed.

  (* 0x8f260 add t5,t5,8; addw t1,t1,8; add a1,a1,1; addw s11,s11,-1 *)
  Lemma cl_dec_adv : forall (x1 x2 x3 x4 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (D n ci B : Z),
    0 <= B <= 40 -> 0 <= ci < n -> n < 67108864 -> 0 <= D < 140737488355328 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 (B + 8)) x7 x8 x9 x10 (Z_to_bv 64 (D + (ci + 1))) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (n - (ci + 1))) x28 x29 (Z_to_bv 64 (B + 8)) x31) FR (Z_to_bv 64 0x8f2c0) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) x7 x8 x9 x10 (Z_to_bv 64 (D + ci)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (n - ci)) x28 x29 (Z_to_bv 64 B) x31) FR (Z_to_bv 64 0x8f2b0) fc None m (seg_rom asegs)).
  Proof.
    intros until B. intros HB HC HN HD K.
    zs. zs. zs. zs.
    replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
    exact K.
  Qed.

  (* 0x8f2d8 addw t4,a7,1; sll a7,a7,32 *)
  Lemma cl_sym_a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (j : Z),
    0 <= j < 320 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (j * 4294967296)) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 (j + 1)) x30 x31) FR (Z_to_bv 64 0x8f330) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 j) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f328) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros HJ K.
    zs. zs. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
    exact K.
  Qed.

  (* 0x8f2e8 srl a1,a7,31 *)
  Lemma cl_sym_b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (j : Z),
    0 <= j < 320 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (2 * j)) x12 x13 x14 x15 x16 (Z_to_bv 64 (j * 4294967296)) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f33c) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (j * 4294967296)) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f338) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros HJ K.
    zs. rewrite Z.shiftr_div_pow2 by lia. replace (j * 4294967296 / 2 ^ 31) with (2 * j) by (change 4294967296 with (2 * 2 ^ 31); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    exact K.
  Qed.

  (* 0x8f304 srl s4,s4,a3; subw s3,t1,a3 *)
  Lemma cl_drop : forall (x1 x2 x3 x4 x5 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (H B hb : Z),
    0 <= H < 2 ^ B -> 0 <= hb <= B -> B <= 40 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) x7 x8 x9 x10 x11 x12 (Z_to_bv 64 hb) x14 x15 x16 x17 x18 (Z_to_bv 64 (B - hb)) (Z_to_bv 64 (H / 2 ^ hb)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f35c) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) x7 x8 x9 x10 x11 x12 (Z_to_bv 64 hb) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 H) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f354) fc None m (seg_rom asegs)).
  Proof.
    intros until hb. intros HH HB B40 K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    zs. rewrite (srl_div H hb) by lia.
    zs.
    exact K.
  Qed.

  (* 0x8f50c sll a1,a7,32; srl a1,a1,31 (the caller then loads lens from slot 400 and adds) *)
  Lemma cl_fill_a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (k : Z),
    0 <= k < 320 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (2 * k)) x12 x13 x14 x15 x16 (Z_to_bv 64 k) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f564) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 k) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f55c) fc None m (seg_rom asegs)).
  Proof.
    intros until k. intros HK K.
    zs. zs. rewrite (zext32_shift31 k) by lia.
    exact K.
  Qed.

  (* 0x8f464 li t2,0; srl a1,s4,a3; subw s3,t1,a3; and a3,a1,7; srl s4,a1,3; add a3,a3,3; addw s3,s3,-3; j 0x8f4fc *)
  Lemma cl_x17 : forall (x1 x2 x3 x4 x5 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (H B hb : Z),
    0 <= H < 2 ^ B -> 1 <= hb -> hb + 3 <= B -> B <= 40 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) (Z_to_bv 64 0) x8 x9 x10 (Z_to_bv 64 (H / 2 ^ hb)) x12 (Z_to_bv 64 (H / 2 ^ hb mod 8 + 3)) x14 x15 x16 x17 x18 (Z_to_bv 64 (B - hb - 3)) (Z_to_bv 64 (H / 2 ^ hb / 8)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f54c) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) x7 x8 x9 x10 x11 x12 (Z_to_bv 64 hb) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 H) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f4b4) fc None m (seg_rom asegs)).
  Proof.
    intros until hb. intros HH HB1 HB B40 K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40. pose proof (drop_bound H B hb ltac:(lia) HH) as DB. pose proof (pow2_le_40 (B - hb) ltac:(lia)) as P40'.
    zs. zs. rewrite (srl_div H hb) by lia.
    zs. zs. replace (Z.land (H / 2 ^ hb) 7) with (H / 2 ^ hb mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    zs. rewrite (Z.shiftr_div_pow2 (H / 2 ^ hb) 3) by lia. change (2 ^ 3) with 8.
    zs. zs. zs.
    replace (B - hb + -3) with (B - hb - 3) by lia.
    exact K.
  Qed.

  (* 0x8f4e0 li t2,0; srl a1,s4,a3; subw s3,t1,a3; and a3,a1,127; srl s4,a1,7; add a3,a3,11; addw s3,s3,-7 *)
  Lemma cl_x18 : forall (x1 x2 x3 x4 x5 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (H B hb : Z),
    0 <= H < 2 ^ B -> 1 <= hb -> hb + 7 <= B -> B <= 40 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) (Z_to_bv 64 0) x8 x9 x10 (Z_to_bv 64 (H / 2 ^ hb)) x12 (Z_to_bv 64 (H / 2 ^ hb mod 128 + 11)) x14 x15 x16 x17 x18 (Z_to_bv 64 (B - hb - 7)) (Z_to_bv 64 (H / 2 ^ hb / 128)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f54c) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) x7 x8 x9 x10 x11 x12 (Z_to_bv 64 hb) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 H) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f530) fc None m (seg_rom asegs)).
  Proof.
    intros until hb. intros HH HB1 HB B40 K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40. pose proof (drop_bound H B hb ltac:(lia) HH) as DB. pose proof (pow2_le_40 (B - hb) ltac:(lia)) as P40'.
    zs. zs. rewrite (srl_div H hb) by lia.
    zs. zs. replace (Z.land (H / 2 ^ hb) 127) with (H / 2 ^ hb mod 128) by (change 127 with (Z.ones 7); rewrite Z.land_ones by lia; reflexivity).
    zs. rewrite (Z.shiftr_div_pow2 (H / 2 ^ hb) 7) by lia. change (2 ^ 7) with 128.
    zs. zs.
    replace (B - hb + -7) with (B - hb - 7) by lia.
    exact K.
  Qed.

  (* repeat-16 pull body, next_in kept in t4: 0x8f3c0 add t6,t4,1; add t1,t1,8; add a1,a1,1; sll t4,t5,t3; add t3,t3,8;
     add s4,t4,s4; addw s11,s11,-1; mv t4,t6 (ld t5,448(s1) at 0x8f3e0 is the caller's) *)
  Lemma cl_padv16 : forall (x1 x2 x3 x4 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (D n ci H B c : Z),
    0 <= c < 256 -> 0 <= B <= 40 -> 0 <= H < 2 ^ B -> 0 <= ci < n -> n < 67108864 -> 0 <= D < 140737488355328 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 (B + 8)) x7 x8 x9 x10 (Z_to_bv 64 (D + (ci + 1))) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (H + c * 2 ^ B)) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (n - (ci + 1))) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (D + (ci + 1))) (Z_to_bv 64 c) (Z_to_bv 64 (D + (ci + 1)))) FR (Z_to_bv 64 0x8f430) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) x7 x8 x9 x10 (Z_to_bv 64 (D + ci)) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 H) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (n - ci)) (Z_to_bv 64 B) (Z_to_bv 64 (D + ci)) (Z_to_bv 64 c) x31) FR (Z_to_bv 64 0x8f410) fc None m (seg_rom asegs)).
  Proof.
    intros until c. intros HC HB HH HCI HN HD K.
    pose proof (pull_bound H B c ltac:(lia) HH HC) as PB. pose proof (pow2_48 (B + 8) ltac:(lia)) as P48.
    zs. zs. zs. zs. zs. zs. rewrite (pull_hold H c B) by lia.
    zs. zs.
    replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
    exact K.
  Qed.

  (* repeat-17 pull body after the byte load: 0x8f358 add t4,t4,1; add t1,t1,8; add a1,a1,1; sll t5,t5,t3; add t3,t3,8;
     add s4,t5,s4; addw s11,s11,-1 (sd t4,496(s1) at 0x8f374 is the caller's) *)
  Lemma cl_padv17 : forall (x1 x2 x3 x4 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (D n ci H B c : Z),
    0 <= c < 256 -> 0 <= B <= 40 -> 0 <= H < 2 ^ B -> 0 <= ci < n -> n < 67108864 -> 0 <= D < 140737488355328 ->
    (forall x30' : word, evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 (B + 8)) x7 x8 x9 x10 (Z_to_bv 64 (D + (ci + 1))) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (H + c * 2 ^ B)) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (n - (ci + 1))) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (D + (ci + 1))) x30' x31) FR (Z_to_bv 64 0x8f3c4) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) x7 x8 x9 x10 (Z_to_bv 64 (D + ci)) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 H) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (n - ci)) (Z_to_bv 64 B) (Z_to_bv 64 (D + ci)) (Z_to_bv 64 c) x31) FR (Z_to_bv 64 0x8f3a8) fc None m (seg_rom asegs)).
  Proof.
    intros until c. intros HC HB HH HCI HN HD K.
    pose proof (pull_bound H B c ltac:(lia) HH HC) as PB. pose proof (pow2_48 (B + 8) ltac:(lia)) as P48.
    zs. zs. zs. zs. zs. zs. rewrite (pull_hold H c B) by lia.
    zs.
    replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
    apply K.
  Qed.

  (* repeat-18 pull body after the byte load: 0x8f428 .. 0x8f444, the same seven instructions as repeat 17 *)
  Lemma cl_padv18 : forall (x1 x2 x3 x4 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (D n ci H B c : Z),
    0 <= c < 256 -> 0 <= B <= 40 -> 0 <= H < 2 ^ B -> 0 <= ci < n -> n < 67108864 -> 0 <= D < 140737488355328 ->
    (forall x30' : word, evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 (B + 8)) x7 x8 x9 x10 (Z_to_bv 64 (D + (ci + 1))) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (H + c * 2 ^ B)) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (n - (ci + 1))) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (D + (ci + 1))) x30' x31) FR (Z_to_bv 64 0x8f494) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) x7 x8 x9 x10 (Z_to_bv 64 (D + ci)) x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 H) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (n - ci)) (Z_to_bv 64 B) (Z_to_bv 64 (D + ci)) (Z_to_bv 64 c) x31) FR (Z_to_bv 64 0x8f478) fc None m (seg_rom asegs)).
  Proof.
    intros until c. intros HC HB HH HCI HN HD K.
    pose proof (pull_bound H B c ltac:(lia) HH HC) as PB. pose proof (pow2_48 (B + 8) ltac:(lia)) as P48.
    zs. zs. zs. zs. zs. zs. rewrite (pull_hold H c B) by lia.
    zs.
    replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
    apply K.
  Qed.

  (* 0x8f48c srl s4,s4,a3; subw s3,t1,a3 *)
  Lemma cl_x16a : forall (x1 x2 x3 x4 x5 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (H B hb : Z),
    0 <= H < 2 ^ B -> 0 <= hb <= B -> B <= 40 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) x7 x8 x9 x10 x11 x12 (Z_to_bv 64 hb) x14 x15 x16 x17 x18 (Z_to_bv 64 (B - hb)) (Z_to_bv 64 (H / 2 ^ hb)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f4e4) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 (Z_to_bv 64 B) x7 x8 x9 x10 x11 x12 (Z_to_bv 64 hb) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 H) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f4dc) fc None m (seg_rom asegs)).
  Proof.
    intros until hb. intros HH HB B40 K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    zs. rewrite (srl_div H hb) by lia.
    zs.
    exact K.
  Qed.

  (* 0x8f49c add a1,a7,-1; sll a1,a1,32; srl a1,a1,31 *)
  Lemma cl_x16b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (j : Z),
    1 <= j < 320 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (2 * (j - 1))) x12 x13 x14 x15 x16 (Z_to_bv 64 j) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f4f8) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 j) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f4ec) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros HJ K.
    zs. zs. zs. replace (j + -1) with (j - 1) by lia. rewrite (zext32_shift31 (j - 1)) by lia.
    exact K.
  Qed.

  (* 0x8f4c8 and a3,s4,3; add a3,a3,3; srl s4,s4,2; addw s3,s3,-2; j 0x8f500 *)
  Lemma cl_x16c : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (H B : Z),
    0 <= H < 2 ^ B -> 2 <= B <= 40 ->
    (evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (H mod 4 + 3)) x14 x15 x16 x17 x18 (Z_to_bv 64 (B - 2)) (Z_to_bv 64 (H / 4)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f550) fc None m (seg_rom asegs))) ->
    evtF asegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 B) (Z_to_bv 64 H) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FR (Z_to_bv 64 0x8f518) fc None m (seg_rom asegs)).
  Proof.
    intros until B. intros HH HB K.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    zs. replace (Z.land H 3) with (H mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
    zs. zs. rewrite (Z.shiftr_div_pow2 H 2) by lia. change (2 ^ 2) with 4.
    zs. zs.
    replace (B + -2) with (B - 2) by lia.
    exact K.
  Qed.
End S.
End CANSEC1.
