(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 722 of its 760 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_blockF.v, with its module paths and module names changed; 9 of its 45 lines of code are new or changed and 724 lines of the source are left out. *)
(* lib/A/Prog/asan_stack_malloc_cF.v -- image A's FOOTPRINT contract of __asan_stack_malloc_<c>, STATEMENT ONLY
   (route (C) wave, a Theorem Labs lane 11:50Z; writer a Theorem Labs lane). Before this file the only generic text was the local copy
   in lib/A/Prog/reac_ctrl_parseF.v (a version not in this delivery), whose comment says the unit's own is to be published; this is it.

   TEXT: fs_shadow_area and asan_stack_malloc_contract_F are the text of record reac_ctrl_parseF.v imports (a Theorem Labs lane's
   NARROW form, a working branch 062bf770c5b fuzz_knock lib/A/Prog/asan_stack_malloc_F.v:694-721,
   with image A's names). reac_ctrl_parseF.v and every other local copy (reac_box_catalogue_matchF.v (not in this delivery),
   ctrl_lay_blockF.v (not in this delivery), reac_box_model_blockF.v (a version not in this delivery)) stay unchanged apart from comment text until the wave-end deletion review.
   Names the text binds: IMG_LO / IMG_HI of lib/A/Prog/ImgBounds.v (the binding parseF.v's text gets through
   reac_ctrl_parse_c.v's `Require Export ImgBounds`), the footprint, rng and evtF of lib/Lib/ExecF.v, and the rest
   of asan_stack_malloc_c.v (fs_B, fs_M, fs_frame, fs_hint, fs_flag, fs_place, FS_SIZE, CF, asan_tls_cells,
   asan_stack_malloc_post, ASAN_STACK_MALLOC_<c>, ASAN_STACK_MALLOC_K).
   One rng premise per region the call reads or writes: the image; the stack window [S0 - K, S0); the five runtime
   pointer cells through DT, TS, C, T and DB; the side stack's header [FS, fs_frame FS 0 0) (hint words, the words at
   FS + 88 and FS + 96, the flag bytes of every class); the class-c frame area [fs_frame FS c 0, + 2^20); that area's
   shadow (fs_shadow_area c bytes); the thread-pointer cells [TP - 88, TP - 80) and [TP - 8, TP + 16).
   No proof is in this file; the proofs are a Theorem Labs lane's. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Definition fs_shadow_area (c : nat) : Z := fs_M c * fs_B c / 8.

Definition asan_stack_malloc_contract_F (c : nat) (entry K : Z) : Prop :=
  (c <= 10)%nat ->
  forall (RNG : lib.Lib.ExecF.footprint) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS : Z) (h DT TS C T DB : word) (k : Z) (flags : list byte),
  let L := bv_unsigned a0 in let TP := bv_unsigned tp in let S0 := bv_unsigned sp in
  1 <= L <= fs_B c -> L mod 8 = 0 ->
  asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
  asan_tls_cells m TP DT TS C T DB k ->
  ((7 <= c)%nat -> bytes_at rsegs m (CF + 120) (le8 (Z_to_bv 64 (2 ^ 64 - 1)))) ->
  bytes_at rsegs m TP (le8 (Z_to_bv 64 FS)) -> fs_place m FS ->
  bytes_at rsegs m (FS + 88) (le8 (Z_to_bv 64 20)) -> bytes_at rsegs m (FS + 96) [Z_to_bv 8 0] ->
  bytes_at rsegs m (fs_hint FS c) (le8 h) ->
  bytes_at rsegs m (fs_flag FS c 0) flags -> Z.of_nat (length flags) = fs_M c ->
  Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
  stk rsegs m lo S0 -> lo + K <= S0 -> FS + FS_SIZE <= S0 - K -> (forall a, S0 - K <= a < S0 -> app_mem a) ->
  disjoint_from [(TP - 88, TP - 80); (TP - 8, TP + 16); (bv_unsigned DT + 8, bv_unsigned DT + 16);
                 (bv_unsigned TS + 8 * k, bv_unsigned TS + 8 * k + 8); (bv_unsigned C + 152, bv_unsigned C + 160);
                 (bv_unsigned T + 48, bv_unsigned T + 64); (bv_unsigned DB + 24, bv_unsigned DB + 32)] (S0 - K) K ->
  rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  rng RNG (S0 - K) K ->
  rng RNG (bv_unsigned DT + 8) 8 -> rng RNG (bv_unsigned TS + 8 * k) 8 -> rng RNG (bv_unsigned C + 152) 8 ->
  rng RNG (bv_unsigned T + 48) 16 -> rng RNG (bv_unsigned DB + 24) 8 ->
  rng RNG FS (fs_frame FS 0 0 - FS) -> rng RNG (fs_frame FS c 0) (2 ^ 20) ->
  rng RNG (shadow_addr (fs_frame FS c 0)) (fs_shadow_area c) ->
  rng RNG (TP - 88) 8 -> rng RNG (TP - 8) 24 ->
  evtF rsegs RNG (asan_stack_malloc_post c K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS h flags lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Definition asan_stack_malloc_0_contract_F : Prop :=
  asan_stack_malloc_contract_F 0 ASAN_STACK_MALLOC_0 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_1_contract_F : Prop :=
  asan_stack_malloc_contract_F 1 ASAN_STACK_MALLOC_1 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_2_contract_F : Prop :=
  asan_stack_malloc_contract_F 2 ASAN_STACK_MALLOC_2 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_6_contract_F : Prop :=
  asan_stack_malloc_contract_F 6 ASAN_STACK_MALLOC_6 ASAN_STACK_MALLOC_K.
