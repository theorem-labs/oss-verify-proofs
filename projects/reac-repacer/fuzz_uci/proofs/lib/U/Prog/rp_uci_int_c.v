(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the contract of rp_uci_int (src/repace_conf.c) on the
   UBSan image, at 0x13240 (frame 32, as the plain image). The UBSan twin of lib/Prog/rp_uci_int_c.v: same models,
   same premises at this image's values, and one premise more for a UBSan trap (below). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
Import ListNotations.
Open Scope Z_scope.

Definition RP_UCI_INT : Z := 0x13240.
Definition RP_UCI_INT_FRAME : Z := 32.

(* the bytes of a reply as the model reads them: Z in [0, 255] *)
Definition zbytes (bs : list byte) : list Z := map (@bv_unsigned 8) bs.

Definition rp_uci_int_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (cur lo : Z),
    (* UBSan only: 0x1326c `beqz s1` traps (unimp at 0x133c4) on reply == NULL, the null-pointer check of
       `reply + n` (repace_conf.c:39). *)
    bv_unsigned a0 <> 0 ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    (* the reply does not run to the end of the address space: without it `end = reply + n` wraps (the
       finding of lib/Prog/rp_uci_int_c.v); on this image the wrap is also the 0x13268 `bltu s2, a0` trap. *)
    bv_unsigned a0 + Z.of_nat (length bs) < 2 ^ 64 ->
    Z.of_nat (length bs) = bv_unsigned a1 ->
    a2 = Z_to_bv 64 cur -> INT_MIN <= cur <= INT_MAX ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_UCI_INT_FRAME <= bv_unsigned sp ->
    bv_unsigned sp <= 2 ^ 63 ->
    bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned sp - RP_UCI_INT_FRAME \/
      bv_unsigned sp <= bv_unsigned a0 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_UCI_INT_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (bv_unsigned a0) bs)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_UCI_INT) fc None m (seg_rom rsegs)).
