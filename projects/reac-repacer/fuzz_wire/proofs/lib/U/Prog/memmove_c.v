(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_pcap proofs/libreac/fuzz_pcap/lib/U/Prog/memmove_c.v at bdfe881c79ce48f2ab686e0aa4ea503bbb4be095, donor pin sha256 83af59086893b5608e2e6e71ea75e7355843d61ec2b20bf3fa1106f362b5e43f, for reac-repacer/fuzz_wire: module paths and image addresses only, entry memmove 0x1c01c (donor) -> 0x1bb0c (this image). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
Import ListNotations.
Open Scope bv_scope.

Definition memmove_entry := 0x1bb0c%Z.

Definition slice (l : list byte) (o k : nat) : list byte := firstn k (skipn o l).

Definition mm_result (us : list byte) (sof dof n : nat) : list byte := upd_bytes us dof (slice us sof n).

Definition memmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (U : Z) (us : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ u8arr rsegs m' U (mm_result us (Z.to_nat (bv_unsigned a1 - U)) (Z.to_nat (bv_unsigned a0 - U)) (Z.to_nat (bv_unsigned a2))).

Definition memmove_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (U : Z) (us : list byte),
  u8arr rsegs m U us ->
  (8 <= U)%Z ->
  (U <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 <= U + Z.of_nat (length us))%Z ->
  (U <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= U + Z.of_nat (length us))%Z ->
  (bv_unsigned a2 < 2^62)%Z ->
  mem_inv rsegs m ->
  evt rsegs (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 U us m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1bb0c) fc None m (seg_rom rsegs)).
