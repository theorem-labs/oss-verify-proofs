(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition Z_BUILD_TREE : Z := 0x1bc50.
Definition Z_BT_STACK : Z := 144.
Definition bt_desc (t : tree_id) : Z := match t with TL => 2904 | TD => 2928 | TB => 2952 end.

Definition build_tree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (t : tree_id) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (dl_As L + 212, dl_As L + DS_SIZE)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ DST m' L (build_tree s t).

Definition build_tree_stmt : Prop :=
  forall (L : dlay) (s : deflate_state) (t : tree_id) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv psegs m -> relro_clean m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_BT_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) ->
  bt_safe s t ->
  a0 = wz (dl_As L) -> a1 = wz (dl_As L + bt_desc t) ->
  evt psegs (build_tree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s t lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_BUILD_TREE) fc None m (seg_rom psegs)).
