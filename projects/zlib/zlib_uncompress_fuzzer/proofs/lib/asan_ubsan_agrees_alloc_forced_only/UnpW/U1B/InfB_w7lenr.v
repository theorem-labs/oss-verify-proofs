(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfAGlue_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import InfPure_w7d InfPure_w7h InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BKit U2BKit_p04. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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

(* [comment removed for export] *)
Lemma swrap32_submod : forall a b, -2147483648 <= a - b < 2147483648 ->
  bv_swrap 32 (a mod 18446744073709551616 - b mod 18446744073709551616) = a - b.
Proof.
  intros a b Hab. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (RNG : footprint) (POST : machine_state -> Prop).

  (* [comment removed for export] *)
  Lemma len_root_a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA lb H : Z),
    0 <= H < 18446744073709551616 -> 1 <= lb <= 15 -> 0 < TA < 140737488355328 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 1) (Z_to_bv 64 (4 * (H mod 2 ^ lb) + TA)) (Z_to_bv 64 (H mod 2 ^ lb)) x13 x14 x15 (Z_to_bv 64 TA) (Z_to_bv 64 1) x18 (Z_to_bv 64 (2 ^ lb - 1)) x21 (Z_to_bv 64 H) x25 x22 x20 x23 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x915f4) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 lb) x12 x13 x14 x15 (Z_to_bv 64 TA) x17 x18 x19 x21 (Z_to_bv 64 H) x25 x22 x20 x23 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x915c0) fc None m (seg_rom bsegs)).
  Proof.
    intros until H. intros HH LB TAR K.
    pose proof (pow2_le_15 lb ltac:(lia)) as P15. pose proof (mod_pow2_bound H lb ltac:(lia)) as MR.
    zs. zs. zs.
    rewrite (mask_sllw lb) by lia.
    zs. rewrite (root_idx H lb) by lia.
    zs. rewrite shl2.
    zs.
    zrung [0x915f4].
    exact K.
  Time Qed.

  (* [comment removed for export] *)
  Lemma len_root_b : forall (x1 x2 x3 x4 x8 x9 x10 x11 x12 x14 x18 x20 x21 x22 x23 x25 x26 x27 x29 x30 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA lb H NX B T1 T2 HV : Z),
    0 <= H < 18446744073709551616 -> 1 <= lb <= 15 -> 0 < TA < 140737488355328 ->
    0 < NX < 140737488355328 -> 0 <= B <= 40 -> 1 <= HV < 67108864 -> 1 <= T1 < 67108864 -> 8 <= T2 < 536870912 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 (B + 8)) (Z_to_bv 64 (T1 + -1)) (Z_to_bv 64 (T2 + -8)) x8 x9 (Z_to_bv 64 1) (Z_to_bv 64 (NX + 1)) (Z_to_bv 64 (H mod 2 ^ lb)) (Z_to_bv 64 (NX + 1)) x14 (Z_to_bv 64 (B + 8)) (Z_to_bv 64 TA) (Z_to_bv 64 1) x18 (Z_to_bv 64 (2 ^ lb - 1)) x21 (Z_to_bv 64 H) x25 x22 x20 x23 x27 x26 (Z_to_bv 64 (NX + 1)) x29 x30 (Z_to_bv 64 (HV + -1))) FR (Z_to_bv 64 0x91618) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 B) (Z_to_bv 64 T1) (Z_to_bv 64 T2) x8 x9 x10 x11 x12 (Z_to_bv 64 (NX + 1)) x14 (Z_to_bv 64 B) (Z_to_bv 64 TA) (Z_to_bv 64 1) x18 (Z_to_bv 64 (2 ^ lb - 1)) x21 (Z_to_bv 64 H) x25 x22 x20 x23 x27 x26 (Z_to_bv 64 NX) x29 x30 (Z_to_bv 64 HV)) FR (Z_to_bv 64 0x916a0) fc None m (seg_rom bsegs)).
  Proof.
    intros until HV. intros HH LB TAR NXR BR HVR T1R T2R K.
    pose proof (pow2_le_15 lb ltac:(lia)) as P15. pose proof (mod_pow2_bound H lb ltac:(lia)) as MR.
    zs. rewrite (root_idx H lb) by lia.
    zs. rewrite shl2.
    zs.
    zrung [0x91618].
    exact K.
  Time Qed.

  (* [comment removed for export] *)
  Lemma len_drop2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x23 x25 x26 x27 x28 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (c1 A5 S6 H : Z),
    0 <= H < 18446744073709551616 -> 0 <= c1 < 4294967296 -> 0 <= code_bits c1 <= 15 -> 0 <= A5 - S6 <= 64 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (code_bits c1)) x11 x12 x13 x14 (Z_to_bv 64 (A5 - S6)) x16 x17 x18 x19 x21 (Z_to_bv 64 (H / 2 ^ code_bits c1)) x25 (Z_to_bv 64 S6) x20 x23 x27 x26 x28 (Z_to_bv 64 (Z.shiftr c1 8)) x30 x31) FR (Z_to_bv 64 0x918c0) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 A5) x16 x17 x18 x19 x21 (Z_to_bv 64 H) x25 (Z_to_bv 64 S6) x20 x23 x27 x26 x28 (Z_to_bv 64 (Z.shiftr c1 8)) x30 x31) FR (Z_to_bv 64 0x918b4) fc None m (seg_rom bsegs)).
  Proof.
    intros until H. intros HH C1R RB AS K.
    pose proof (cw_land31 c1 RB) as L31. pose proof (cw_shr8_range c1 C1R) as S8R.
    zs. rewrite (swrap32_submod A5 S6) by lia.
    zs. rewrite ?(Z.mod_small (Z.shiftr c1 8)) by lia. rewrite L31.
    zs. rewrite (srl_div H (code_bits c1)) by lia.
    exact K.
  Time Qed.

  (* [comment removed for export] *)
  Lemma len_six_a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA c1 H : Z),
    0 <= H < 18446744073709551616 -> 0 <= c1 < 4294967296 -> 1 <= code_bits c1 <= 15 -> 1 <= code_op c1 -> code_bits c1 + code_op c1 <= 15 -> 0 < TA < 140737488355328 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 (Z_to_bv 64 (4 * (H mod 2 ^ (code_bits c1 + code_op c1) / 2 ^ code_bits c1 + code_val c1) + TA)) (Z_to_bv 64 (H mod 2 ^ (code_bits c1 + code_op c1) / 2 ^ code_bits c1 + code_val c1)) x14 x15 (Z_to_bv 64 TA) (Z_to_bv 64 1) x18 (Z_to_bv 64 (code_val c1)) (Z_to_bv 64 (2 ^ (code_bits c1 + code_op c1) - 1)) (Z_to_bv 64 H) x25 x22 x20 x23 x27 x26 x28 x29 (Z_to_bv 64 (code_bits c1)) x31) FR (Z_to_bv 64 0x9177c) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 c1) x13 x14 x15 (Z_to_bv 64 TA) (Z_to_bv 64 1) x18 x19 x21 (Z_to_bv 64 H) x25 x22 x20 x23 x27 x26 x28 x29 (Z_to_bv 64 (code_bits c1)) x31) FR (Z_to_bv 64 0x91714) fc None m (seg_rom bsegs)).
  Proof.
    intros until H. intros HH C1R RB OP1 OP15 TAR K.
    pose proof (cw_landE000 c1 ltac:(lia)) as LE0. pose proof (code_val_range c1) as VALR.
    set (rb := code_bits c1) in *. set (op := code_op c1) in *.
    pose proof (pow2_le_15 (rb + op) ltac:(lia)) as P15. pose proof (pow2_le_15 rb ltac:(lia)) as PRB. pose proof (pow2_le_15 op ltac:(lia)) as POP.
    pose proof (mod_pow2_bound H (rb + op) ltac:(lia)) as MR. pose proof (sidx_range rb op H ltac:(lia) ltac:(lia)) as JR.
    zs. zs. rewrite LE0.
    zrung [0x91728]. change (Z.land c1 255) with op.
    zrung [0x91738].
    zs. rewrite (code_word_val c1 C1R). set (val := code_val c1) in *.
    zs. zs. zs.
    rewrite (mask_sllw (rb + op)) by lia.
    zs. rewrite (InfAGlue_w7.land_mask_mod H (rb + op)) by lia.
    zs. rewrite (srlw_wrap_small (H mod 2 ^ (rb + op)) rb) by lia.
    zs. zs. zs. rewrite (zext32_shift30 (H mod 2 ^ (rb + op) / 2 ^ rb + val)) by lia.
    zrung [0x9177c].
    rewrite (Z.mod_small (H mod 2 ^ (rb + op) / 2 ^ rb + val)) by lia.
    exact K.
  Time Qed.

  (* [comment removed for export] *)
  Lemma len_six_b : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x18 x20 x22 x25 x26 x27 x28 x29 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA rb op val H B bz : Z),
    0 <= B <= 40 -> 0 <= H < 2 ^ B -> 0 <= bz < 256 -> 1 <= rb <= 15 -> 1 <= op -> rb + op <= 15 -> 0 <= val < 65536 -> 0 < TA < 140737488355328 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 ((H + bz * 2 ^ B) mod 2 ^ (rb + op) / 2 ^ rb + val)) (Z_to_bv 64 (4 * ((H + bz * 2 ^ B) mod 2 ^ (rb + op) / 2 ^ rb + val) + TA)) x12 (Z_to_bv 64 (Z.shiftl ((H + bz * 2 ^ B) mod 2 ^ (rb + op) / 2 ^ rb + val) 32)) x14 x15 (Z_to_bv 64 TA) (Z_to_bv 64 1) x18 (Z_to_bv 64 val) (Z_to_bv 64 (2 ^ (rb + op) - 1)) (Z_to_bv 64 (H + bz * 2 ^ B)) x25 x22 (Z_to_bv 64 B) x20 x27 x26 x28 x29 (Z_to_bv 64 rb) x31) FR (Z_to_bv 64 0x9183c) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 bz) x11 x12 x13 x14 x15 (Z_to_bv 64 TA) (Z_to_bv 64 1) x18 (Z_to_bv 64 val) (Z_to_bv 64 (2 ^ (rb + op) - 1)) (Z_to_bv 64 H) x25 x22 (Z_to_bv 64 B) x20 x27 x26 x28 x29 (Z_to_bv 64 rb) x31) FR (Z_to_bv 64 0x91814) fc None m (seg_rom bsegs)).
  Proof.
    intros until bz. intros BR HH BZ RB OP1 OP15 VAL TAR K.
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
    zs. zs. zs. rewrite (zext32_shift30 (H1 mod 2 ^ (rb + op) / 2 ^ rb + val)) by lia.
    zrung [0x9183c].
    exact K.
  Time Qed.

  (* [comment removed for export] *)
  Lemma len_six_c : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x15 x16 x18 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (TA idx B S6 HV NX1 : Z),
    0 <= B <= 64 -> 0 <= idx < 4294967296 -> 0 < TA < 140737488355328 -> 1 <= HV < 67108864 -> 0 < NX1 < 140737488355328 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 1) (Z_to_bv 64 NX1) (Z_to_bv 64 NX1) (Z_to_bv 64 idx) (Z_to_bv 64 (HV + -1)) x15 x16 (Z_to_bv 64 1) x18 x19 x21 x24 x25 (Z_to_bv 64 (S6 + -8)) (Z_to_bv 64 (B + 8)) x20 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x9178c) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (4 * idx + TA)) (Z_to_bv 64 NX1) (Z_to_bv 64 (Z.shiftl idx 32)) (Z_to_bv 64 HV) x15 x16 (Z_to_bv 64 1) x18 x19 x21 x24 x25 (Z_to_bv 64 S6) (Z_to_bv 64 B) x20 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x91848) fc None m (seg_rom bsegs)).
  Proof.
    intros until NX1. intros BR IR TAR HVR NXR K.
    zrung [0x9178c].
    rewrite (Z.mod_small idx) by lia.
    exact K.
  Time Qed.

  (* [comment removed for export] *)
  Lemma len_join1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (c : Z),
    0 <= c < 4294967296 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (Z.shiftl (code_val c) 16)) x11 (Z_to_bv 64 c) x13 x14 x15 x16 x17 x18 x19 x21 x24 x25 x22 x20 x23 x27 x26 x28 (Z_to_bv 64 (Z.shiftr c 8)) (Z_to_bv 64 (code_bits c)) x31) FR (Z_to_bv 64 0x9165c) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (code_val c)) x11 (Z_to_bv 64 (Z.land c 65535)) x13 x14 x15 x16 x17 x18 x19 x21 x24 x25 x22 x20 x23 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x9164c) fc None m (seg_rom bsegs)).
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
  Lemma len_join2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (c rb : Z),
    0 <= c < 4294967296 -> 1 <= rb <= 15 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (code_bits c + rb)) x11 (Z_to_bv 64 c) x13 x14 x15 x16 x17 x18 x19 x21 x24 x25 x22 x23 x20 x27 (Z_to_bv 64 (Z.shiftr c 8)) x28 x29 (Z_to_bv 64 rb) x31) FR (Z_to_bv 64 0x917d4) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (code_val c)) x11 (Z_to_bv 64 (Z.land c 65535)) x13 x14 x15 x16 x17 x18 x19 x21 x24 x25 x22 x23 x20 x27 x26 x28 x29 (Z_to_bv 64 rb) x31) FR (Z_to_bv 64 0x917c0) fc None m (seg_rom bsegs)).
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

  (* [comment removed for export] *)
  Lemma len_ck1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A sb : Z),
    0 <= A < 140737488355328 -> (sb = 0 \/ (0 < sb <= 7 /\ A mod 8 + 1 - 1 < sb)) ->
    (forall y : word, evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y (Z_to_bv 64 A) (Z_to_bv 64 sb) x13 x14 x15 x16 x17 x18 x19 x21 x24 x25 x22 x20 x23 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x91694) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) (Z_to_bv 64 sb) x13 x14 x15 x16 x17 x18 x19 x21 x24 x25 x22 x20 x23 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x91690) fc None m (seg_rom bsegs)).
  Proof.
    intros until sb. intros AR CK K.
    ck_branchJ 10 0x91694 CK.
    apply K.
  Time Qed.
  Lemma len_ck2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A sb : Z),
    0 <= A < 140737488355328 -> (sb = 0 \/ (0 < sb <= 7 /\ A mod 8 + 1 - 1 < sb)) ->
    (forall y : word, evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y (Z_to_bv 64 A) x12 (Z_to_bv 64 sb) x14 x15 x16 x17 x18 x19 x21 x24 x25 x22 x23 x20 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x9180c) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 (Z_to_bv 64 sb) x14 x15 x16 x17 x18 x19 x21 x24 x25 x22 x23 x20 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x91808) fc None m (seg_rom bsegs)).
  Proof.
    intros until sb. intros AR CK K.
    ck_branchJ 10 0x9180c CK.
    apply K.
  Time Qed.

  (* [comment removed for export] *)
  Lemma len_prep : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (B HV : Z),
    0 <= B <= 40 -> 0 <= HV < 67108864 ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 (Z_to_bv 64 B) (Z_to_bv 64 HV) (Z_to_bv 64 (8 * HV)) x8 x9 (Z_to_bv 64 (Z.shiftl B 32)) x11 x12 x13 (Z_to_bv 64 HV) (Z_to_bv 64 B) x16 x17 x18 x19 (Z_to_bv 64 (Z.shiftl HV 32)) x24 x25 (Z_to_bv 64 B) x20 x23 x27 x26 x28 x29 x30 (Z_to_bv 64 HV)) FR (Z_to_bv 64 0x91610) fc None m (seg_rom bsegs)) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 HV) x15 x16 x17 x18 x19 x21 x24 x25 (Z_to_bv 64 B) x20 x23 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x915f4) fc None m (seg_rom bsegs)).
  Proof.
    intros until HV. intros BR HVR K.
    assert (SH : 0 <= Z.shiftl HV 32 < 18446744073709551616) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 32) with 4294967296; lia).
    assert (SB : 0 <= Z.shiftl B 32 < 18446744073709551616) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 32) with 4294967296; lia).
    zrung [0x91610].
    rewrite (shl32_shr32 B), (shl32_shr32 HV), (shl32_shr29 HV).
    exact K.
  Time Qed.

  (* [comment removed for export] *)
  Lemma lenx_ck : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (FR : bvmap 5 word) (fc : bv 32) (m : amem) (A sb : Z),
    0 <= A < 140737488355328 -> (sb = 0 \/ (0 < sb <= 7 /\ A mod 8 + 1 - 1 < sb)) ->
    (forall y : word, evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y (Z_to_bv 64 A) x12 x13 (Z_to_bv 64 sb) x15 x16 x17 x18 x19 x21 x24 x25 x22 x20 x23 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x8e44c) fc None m (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 (Z_to_bv 64 sb) x15 x16 x17 x18 x19 x21 x24 x25 x22 x20 x23 x27 x26 x28 x29 x30 x31) FR (Z_to_bv 64 0x8e448) fc None m (seg_rom bsegs)).
  Proof.
    intros until sb. intros AR CK K.
    ck_branchJ 10 0x8e44c CK.
    apply K.
  Time Qed.
End S.
End CANSEC1.
