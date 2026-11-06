(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated unchanged from an earlier relocation of this file for fuzz_command, for the image this tree pins (fuzz_command.asan sha256 c0661b96). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_strcpyw.v, with its addresses and numbers changed; 300 of its 376 lines of code are new or changed and 371 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_atoiw.v, with its module paths, addresses and numbers changed; 94 of its 182 lines of code are new or changed and 288 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Bz/A/I_strtolw.v, with its module paths, module names and addresses changed; 23 of its 43 lines of code are new or changed and 162 lines of the source are left out. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Spec Require Import CType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import __intscan_c.
Import ListNotations.
Open Scope Z_scope.

Definition STRTOL : Z := 0x1ce98.
Definition STRTOL_SSP_GOT : Z := 0x1f3e8.
Definition STRTOL_SSP_GUARD : Z := 0x509d0.

Definition strtol_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A Ep : Z) (str : list byte) (ev : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (s10_val str)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 368, bv_unsigned sp); (Ep, Ep + 8); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' Ep [C8 (Z_to_bv 64 (A + s10_end str))]
    /\ rw_cells rsegs m' (bv_unsigned tp + -164) [C4 (s10_errno str ev)].

Definition strtol_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Ep : Z) (str : list byte) (ev can e0 : word) (lo : Z),
    bytes_at rsegs m A (str ++ [Z_to_bv 8 0]) -> A + Z.of_nat (length str) + 1 < 2^64 ->
    0 < Ep -> rw_cells rsegs m Ep [C8 e0] ->
    rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] ->
    bytes_at rsegs m STRTOL_SSP_GOT (le8 (Z_to_bv 64 STRTOL_SSP_GUARD)) -> bytes_at rsegs m STRTOL_SSP_GUARD (le8 can) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 368 <= bv_unsigned sp ->
    (A + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= A) ->
    (Ep + 8 <= lo \/ bv_unsigned sp <= Ep) ->
    (bv_unsigned tp + -164 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164) ->
    (Ep + 8 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= Ep) ->
    (STRTOL_SSP_GOT + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GOT) ->
    (STRTOL_SSP_GUARD + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GUARD) ->
    (STRTOL_SSP_GUARD + 8 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= STRTOL_SSP_GUARD) ->
    (STRTOL_SSP_GUARD + 8 <= Ep \/ Ep + 8 <= STRTOL_SSP_GUARD) ->
    mem_inv rsegs m ->
    evt rsegs (strtol_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A Ep str ev lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 Ep) (Z_to_bv 64 10) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRTOL) fc None m (seg_rom rsegs)).
