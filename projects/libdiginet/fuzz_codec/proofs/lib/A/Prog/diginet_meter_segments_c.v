(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/diginet_meter_segments_c.v, with its module paths, module names and addresses changed; 5 of its 19 lines of code are new or changed and 6 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-A form of lib/Prog/diginet_meter_segments_c.v for fuzz_decode.asan, in the form of projects/libreac/fuzz_decode/proofs/lib/A/Prog/reac_upstream_channels_c.v (a leaf with no stack frame). *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/libdiginet/fuzz_decode/lib/A/Prog/diginet_meter_segments_c.v (fuzz_decode.asan, image A, a code-identical twin) to fuzz_codec.asan, image A: entry 0x855c8, the image segments lib/A/AWalkFw0.v tfibsegs, module paths changed. *)
(* diginet_meter_segments on fuzz_codec.asan (image A): entry 0x855c8, 56 bytes (14 instructions).

   Contract. The argument a0 is the uint16_t mask, zero-extended by the caller, so 0 <= mask < 2^16. The result in
   a0 is DgnLib.v's diginet_meter_segments mask, sign-extended to 64 bits: the result of the plain contract
   lib/Prog/diginet_meter_segments_c.v. The function writes a1 and a2. It keeps all other registers and the memory.

   Facts read off fuzz_codec.asan: the 14 instructions at 0x855c8-0x855fc are the plain image's 0x1575c-0x15790 word
   for word (the branch and jump offsets are pc-relative): 0x855c8 `addi a1, zero, 0`; the loop 0x855cc-0x855e0
   (`srlw`, `andi 1`, `beq` to 0x855e8, `addiw 1`, `addi a2, zero, 14`, `bne` back to 0x855cc), 0x855e4 `jal zero`
   to 0x855ec, 0x855e8 `addi a2, a1, 0`; then 0x855ec-0x855f8 `srlw`, `sltiu 1`, `addiw -1`, `or`, and 0x855fc
   `jalr zero, 0(ra)`. No stack frame, no load, no store, no call, no shadow check. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnLib.
Open Scope Z_scope.

Definition DIGINET_METER_SEGMENTS_PC : Z := 0x855c8.

Definition diginet_meter_segments_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mask : Z),
    0 <= mask < 2^16 ->
    evt tfibsegs
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (diginet_meter_segments mask)) a1' a2' a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom tfibsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mask) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_METER_SEGMENTS_PC) fc None m (seg_rom tfibsegs)).
