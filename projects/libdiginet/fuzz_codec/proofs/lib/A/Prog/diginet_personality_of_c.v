(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/diginet_personality_of_c.v, with its module paths, module names and addresses changed; 9 of its 23 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-A form of lib/Prog/diginet_personality_of_c.v for fuzz_decode.asan, in the form of projects/libreac/fuzz_decode/proofs/lib/A/Prog/reac_upstream_channels_c.v (a leaf with no stack frame), with the image's own table address. *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/libdiginet/fuzz_decode/lib/A/Prog/diginet_personality_of_c.v (fuzz_decode.asan, image A, a code-identical twin) to fuzz_codec.asan, image A: entry 0x84888 and the personalities table 0x9d920, the image segments lib/A/AWalkFw0.v tfibsegs, module paths changed; the premise on desk widened from -2^31 <= desk < 2^31 to 0 <= desk < 2^64 (any 64-bit a0: the code compares the whole register with 1 and 2). *)
(* diginet_personality_of on fuzz_codec.asan (image A): entry 0x84888, 44 bytes (11 instructions).

   Contract. The argument a0 is the register value desk, any 64-bit value 0 <= desk < 2^64 (the code compares the
   whole register with 1 and 2). The result in a0 is personality_ptr_A (diginet_personality_of desk): &personalities[0] for
   desk 1, &personalities[1] for desk 2, 0 (NULL) for any other desk, the result of the plain contract
   lib/Prog/diginet_personality_of_c.v at this image's table address. The function writes a1 and a2. It keeps all
   other registers and the memory.

   Facts read off fuzz_codec.asan:
   - the table: 0x8488c `auipc a0, 0x19` and 0x84894 `addi a0, a0, 0x94` give 0x8488c + 0x19000 + 0x94 = 0x9d920,
     the symtab's `personalities` (STT_OBJECT at 0x9d920, 96 bytes with its redzone); its entries are 24 bytes
     apart (0x848a4 `addi a0, a0, 0x18`), so &personalities[i] = 0x9d920 + 24 * i. The plain image's table is at
     0x1f3f8;
   - 0x84888 `addi a1, a0, 0` (desk), 0x84890 `addi a2, zero, 1`, 0x84898 `beq a1, a2` to 0x848b0: desk 1 returns
     with a0 = 0x9d920;
   - otherwise 0x8489c `addi a1, a1, -2`, 0x848a0 `sltu a1, zero, a1` (desk <> 2), 0x848a4 `addi a0, a0, 0x18`,
     0x848a8 `addi a1, a1, -1`, 0x848ac `and a0, a1, a0`: 0x9d938 for desk 2, 0 otherwise; 0x848b0
     `jalr zero, 0(ra)`.
   No stack frame, no load, no store, no call, no shadow check. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
Open Scope Z_scope.

Definition DIGINET_PERSONALITY_OF : Z := 0x84888.

(* The image-A address of personalities (symtab, and the auipc / addi at 0x8488c / 0x84894). *)
Definition PERSONALITIES_A : Z := 0x9d920.

(* The C pointer of a DgnLib.v personality index at image A: &personalities[i], or NULL (DgnLayout.v's
   personality_ptr at this image's table address). *)
Definition personality_ptr_A (p : option Z) : Z :=
  match p with Some i => PERSONALITIES_A + 24 * i | None => 0 end.

Definition diginet_personality_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (desk : Z),
    0 <= desk < 2^64 ->
    evt tfibsegs
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (personality_ptr_A (diginet_personality_of desk))) a1' a2' a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom tfibsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 desk) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_PERSONALITY_OF) fc None m (seg_rom tfibsegs)).
