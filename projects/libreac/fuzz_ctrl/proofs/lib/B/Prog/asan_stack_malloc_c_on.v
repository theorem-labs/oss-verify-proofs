(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 722 of its 760 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_blockF.v; 18 of its 37 lines of code are new or changed and 741 lines of the source are left out. *)
(* lib/B/Prog/asan_stack_malloc_c_on.v -- route (C) (a Theorem Labs lane 09:20Z; a Theorem Labs lane wave L1, writer a Theorem Labs lane): the ADDITIVE
   `_on` form of asan_stack_malloc_c.v's contract, STATEMENT ONLY. asan_stack_malloc_c.v stays byte-identical.

   THERE IS NO PROOF of either form on fuzz_ctrl (a Theorem Labs lane 09:44Z: statements only; lib/A/Tk/AW/Sm6.v proves image A's class-6 forms, not these). The `_on` contract is STRONGER than
   the original, so NO proof may assume it until it is proved; whoever proves the walk confirms or fixes R.
   R (from the statement and a Theorem Labs lane's measurement, 09:36Z): malloc_6 READS no shadow: its constant loads are .got
   pointers, the class-6 fake-stack flag byte 0x3dc30, and the GOT_UAR pointer it dereferences at 0x3dc50 (a Theorem Labs lane
   audit), and it WRITES the shadow of a frame the RUN chooses (asan_stack_malloc_frame's munch row
   [shadow_addr fr, shadow_addr fr + n), fr = fs_frame FS c j, 0 <= j < fs_M c). The class c is a PARAMETER of the
   contract, so a pre-call R names the shadow of the class-c BLOCK, which holds every frame the run can choose:
   R = [shadow_addr (fs_frame FS c 0), shadow_addr (fs_frame FS c 0) + 131072) (the block is fs_M c * fs_B c = 2^20
   bytes, so its shadow is 2^20 / 8 = 131072 bytes, for every c). a Theorem Labs lane's walks Sm0/1/2/6.v (not in this delivery) use the
   premise only in shadow_stk over this range. Wave decision a Theorem Labs lane 10:57Z (report
   side-stack-shadow.md (a working note, not in this delivery)): the WHOLE side-stack shadow (the 10:2xZ form) is
   NOT dischargeable at a cut. Its first 4608 bytes shadow the header and flags, and AR does not make them present.
   The class block lies in the frames area [FS + 36864, FS + FS_SIZE), whose shadow AR's am_areas makes present
   (Reusable/YG0n.v:137-139, :220) and which cut_shadow gains as fs_area_shadow.
   LOAD-BEARING PREMISE for R (a Theorem Labs lane audit, 10:38Z): `bytes_at m (FS + 96) [Z_to_bv 8 0]` makes the beqz at 0x3dbc8 skip
   FakeStack::GC (0x3d2a8), which would otherwise store shadow over the class block (sd loop 0x3d468-0x3d484, inside R)
   AND call PoisonShadow (0x54358) at 0x3d3c4 over the THREAD STACK, outside R. Whoever drops or weakens that premise
   must widen R to the thread-stack shadow or keep the premise.
   POST: unchanged; asan_stack_malloc_post states no shadow fact. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c.
Import ListNotations.
Open Scope Z_scope.

(* The shadow of the fake stack's class-c BLOCK [fs_frame FS c 0, fs_frame FS c 0 + 2^20): every frame of class c
   (fs_frame FS c j, 0 <= j < fs_M c) has its shadow inside it (see the header). *)
Definition asan_stack_malloc_shadow_R (FS : Z) (c : nat) : Z -> Prop :=
  fun a => shadow_addr (fs_frame FS c 0) <= a < shadow_addr (fs_frame FS c 0) + 131072.

Definition asan_stack_malloc_contract_on (c : nat) (entry K : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS : Z) (h DT TS C T DB : word) (k : Z) (flags : list byte),
  let L := bv_unsigned a0 in let TP := bv_unsigned tp in let S0 := bv_unsigned sp in
  1 <= L <= fs_B c -> L mod 8 = 0 ->
  asan_cells m -> shadow_rw_on (asan_stack_malloc_shadow_R FS c) m -> mem_inv rsegs m ->
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
  evt rsegs (asan_stack_malloc_post c K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS h flags lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Definition asan_stack_malloc_0_contract_on : Prop :=
  asan_stack_malloc_contract_on 0 ASAN_STACK_MALLOC_0 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_1_contract_on : Prop :=
  asan_stack_malloc_contract_on 1 ASAN_STACK_MALLOC_1 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_2_contract_on : Prop :=
  asan_stack_malloc_contract_on 2 ASAN_STACK_MALLOC_2 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_6_contract_on : Prop :=
  asan_stack_malloc_contract_on 6 ASAN_STACK_MALLOC_6 ASAN_STACK_MALLOC_K.
