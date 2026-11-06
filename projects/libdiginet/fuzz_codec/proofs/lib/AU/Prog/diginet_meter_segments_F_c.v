(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/diginet_meter_segments_c.v, with its module paths, module names and addresses changed; 9 of its 21 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-B (fuzz_decode.asan-ubsan) text of lib/A/Prog/diginet_meter_segments_F_c.v, in the leaf form of proofs/libreac/fuzz_decode/lib/B/Prog/check_braid_F_c.v at recipes commit 88154566652a, with this image's entry. *)
(* Footprint form of the contract of diginet_meter_segments on fuzz_decode.asan-ubsan (image B): entry 0x82dc8,
   56 bytes (14 instructions), no call, no stack frame.

   Contract. The argument a0 is the uint16_t mask, zero-extended by the caller, so 0 <= mask < 2^16. The result in a0
   is DgnLib.v's diginet_meter_segments mask, sign-extended to 64 bits. The function writes a1 and a2. It keeps all
   other registers and the memory. The run is an ExecF.evtF run under a footprint RNG; the code loads nothing and
   stores nothing, so it makes no data access and the contract holds for every RNG: there is no rng premise.

   Facts read off fuzz_decode.asan-ubsan (sha256 1c8e7ec20682...; symtab of its unstripped twin 50d7282d5a4b...): the
   14 instructions at 0x82dc8-0x82dfc are image A's 0x82af8-0x82b2c word for word (the branch and jump offsets are
   pc-relative): 0x82dc8 `addi a1, zero, 0`; the loop 0x82dcc-0x82de0 (`srlw a2, a0, a1`, `andi a2, a2, 1`, `beq a2,
   zero` to 0x82de8, `addiw a1, a1, 1`, `addi a2, zero, 14`, `bne a1, a2` back to 0x82dcc), 0x82de4 `jal zero` to
   0x82dec, 0x82de8 `addi a2, a1, 0`; then 0x82dec-0x82df8 `srlw a0, a0, a2`, `sltiu a0, a0, 1`, `addiw a0, a0, -1`,
   `or a0, a0, a2`, and 0x82dfc `jalr zero, 0(ra)`.
   UBSan trap words: none (no `unimp` in the 14 words), so the contract takes no UBSan premise. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import ExecF.
Open Scope Z_scope.

Definition DIGINET_METER_SEGMENTS_PC : Z := 0x85f14.

Definition diginet_meter_segments_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mask : Z),
    0 <= mask < 2^16 ->
    ExecF.evtF tfibsegs RNG
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (diginet_meter_segments mask)) a1' a2' a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom tfibsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mask) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_METER_SEGMENTS_PC) fc None m (seg_rom tfibsegs)).
