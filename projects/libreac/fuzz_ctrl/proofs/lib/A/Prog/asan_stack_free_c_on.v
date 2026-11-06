(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1441 of its 1505 lines of code are new or changed and 947 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/YTail.v, with its module paths and module names changed; 534 of its 819 lines of code are new or changed and 1220 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/YTailF.v, with its module paths and module names changed; 59 of its 90 lines of code are new or changed and 788 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/asan_stack_free_cF.v; 10 of its 38 lines of code are new or changed and 62 lines of the source are left out. *)
(* lib/A/Prog/asan_stack_free_c_on.v -- route (C) (a Theorem Labs lane 09:20Z; a Theorem Labs lane's wave, writer a Theorem Labs lane): the ADDITIVE
   `_on` form of asan_stack_free_c.v's contract, STATEMENT ONLY. asan_stack_free_c.v stays byte-identical.

   THERE IS NO PROOF of either form IN THIS FILE (both are proved at lib/A/Tk/AW/Sf6.v:82 / :179; a Theorem Labs lane 09:44Z: statements only; the general-footprint walk is
   a Theorem Labs lane's asan_stack_freeF.v, lib/A/Prog/asan_stack_freeF.v in this tree). The `_on` contract is STRONGER than the original (weaker
   premise, preservation post), so NO proof may assume it until it is proved; whoever proves the walk confirms or fixes R.
   R (from the statement and a Theorem Labs lane's measurement, 09:36Z): free_6 READS no shadow (its one constant load, 0x3dc18, is the
   .rodata cell 0x10338) and WRITES the frame's shadow [shadow_addr fr, shadow_addr fr + n), fr = fs_frame FS c j,
   n = fs_shadow_n c L (the post's munch row). A shadow store needs the byte present and writable, which is what
   shadow_rw_on gives, so R is that written range.
   POST: `shadow_rw m'` -> `forall P, shadow_rw_on P m -> shadow_rw_on P m'` (wave form, a Theorem Labs lane 09:38Z). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c asan_stack_free_c.
Import ListNotations.
Open Scope Z_scope.

(* The shadow bytes the run needs present and writable: the frame's shadow it fills with 0xf5. *)
Definition asan_stack_free_shadow_R (c : nat) (L FS j : Z) (a : Z) : Prop :=
  shadow_addr (fs_frame FS c j) <= a < shadow_addr (fs_frame FS c j) + fs_shadow_n c L.

Definition asan_stack_free_post_on (c : nat) (K : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (L FS j lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    let fr := fs_frame FS c j in let n := fs_shadow_n c L in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(fs_flag FS c j, fs_flag FS c j + 1); (shadow_addr fr, shadow_addr fr + n);
              (bv_unsigned sp - K, bv_unsigned sp)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ fs_place m' FS
    /\ bytes_at rsegs m' (fs_flag FS c j) [Z_to_bv 8 0]
    /\ bytes_at rsegs m' (shadow_addr fr) (repeat (Z_to_bv 8 0xf5) (Z.to_nat n))
    /\ asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m').

Definition asan_stack_free_contract_on (c : nat) (entry K : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS j : Z),
  let fr := bv_unsigned a0 in let L := bv_unsigned a1 in let S0 := bv_unsigned sp in
  0 <= j < fs_M c -> fr = fs_frame FS c j ->
  1 <= L <= fs_B c -> L mod 8 = 0 ->
  fs_place m FS ->
  bytes_at rsegs m (fs_flag FS c j) [Z_to_bv 8 1] ->
  bytes_at rsegs m (fr + fs_B c - 8) (le8 (Z_to_bv 64 (fs_flag FS c j))) ->
  asan_cells m -> shadow_rw_on (asan_stack_free_shadow_R c L FS j) m -> mem_inv rsegs m ->
  stk rsegs m lo S0 -> lo + K <= S0 -> FS + FS_SIZE <= S0 - K ->
  HIGHMEM_BEG <= lo -> S0 <= APPMEM_END ->
  evt rsegs (asan_stack_free_post_on c K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS j lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Definition asan_stack_free_6_contract_on : Prop :=
  asan_stack_free_contract_on 6 ASAN_STACK_FREE_6 ASAN_STACK_FREE_K.
