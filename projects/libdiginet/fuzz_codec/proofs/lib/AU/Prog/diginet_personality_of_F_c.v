(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/diginet_personality_of_c.v, with its module paths, module names and addresses changed; 9 of its 23 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-A form of lib/Prog/diginet_personality_of_c.v for fuzz_decode.asan, in the form of projects/libreac/fuzz_decode/proofs/lib/A/Prog/reac_upstream_channels_c.v (a leaf with no stack frame), with the image's own table address. *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/libdiginet/fuzz_decode/lib/A/Prog/diginet_personality_of_c.v (fuzz_decode.asan, image A, a code-identical twin) to fuzz_codec.asan, image A: entry 0x84888 and the personalities table 0x9d920, the image segments lib/A/AWalkFw0.v tfibsegs, module paths changed; the premise on desk widened from -2^31 <= desk < 2^31 to 0 <= desk < 2^64 (any 64-bit a0: the code compares the whole register with 1 and 2). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_personality_of_c.v, with its module paths and addresses changed; 9 of its 25 lines of code are new or changed and 7 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-B (fuzz_decode.asan-ubsan) text of lib/A/Prog/diginet_personality_of_F_c.v, in the leaf form of proofs/libreac/fuzz_decode/lib/B/Prog/check_braid_F_c.v at recipes commit 88154566652a, with this image's entry and table address. *)
(* Footprint form of the contract of diginet_personality_of on fuzz_decode.asan-ubsan (image B): entry 0x82938,
   56 bytes (13 instructions and the UBSan trap word at 0x8296c), no call, no stack frame.

   Contract. The argument a0 is the enum diginet_desk desk, an int the caller sign-extends to 64 bits, so
   -2^31 <= desk < 2^31. The result in a0 is personality_ptr_B (diginet_personality_of desk): &personalities[0] for
   desk 1, &personalities[1] for desk 2, 0 (NULL) for any other desk (lib/Spec/DgnLib.v's diginet_personality_of at
   this image's table address). The function writes a1 (the result names a1' and a2'). It keeps all other registers
   and the memory. The run is an ExecF.evtF run under a footprint RNG; the code loads nothing and stores nothing, so it
   makes no data access and the contract holds for every RNG: there is no rng premise.

   Facts read off fuzz_decode.asan-ubsan (sha256 1c8e7ec20682...; symtab of its unstripped twin 50d7282d5a4b...):
   - 0x82938 `addi a1, zero, 1`, 0x8293c `beq a0, a1` to 0x82958: desk 1 goes to 0x82958 `auipc a0, 0x18` and
     0x8295c `addi a0, a0, 0x1c8`, so a0 = 0x82958 + 0x18000 + 0x1c8 = 0x9ab20, then 0x82960 `jalr zero, 0(ra)`;
   - 0x82940 `addi a1, zero, 2`, 0x82944 `bne a0, a1` to 0x82964: any desk other than 1 and 2 goes to 0x82964
     `addi a0, zero, 0` and 0x82968 `jalr zero, 0(ra)`;
   - desk 2: 0x82948 `auipc a0, 0x18` and 0x8294c `addi a0, a0, 0x1f0` give a0 = 0x82948 + 0x18000 + 0x1f0 =
     0x9ab38, then the UBSan null check 0x82950 `beqz a0` to the trap word 0x8296c (`unimp`, 0xc0001073), then
     0x82954 `jalr zero, 0(ra)`;
   - the symtab's `personalities` is the STT_OBJECT at 0x9ab20 (96 bytes with its redzone); its entries are 24 bytes
     apart (0x9ab38 - 0x9ab20), so &personalities[i] = 0x9ab20 + 24 * i.
   UBSan trap word: one, 0x8296c. The check 0x82950 tests the constant 0x9ab38 that 0x82948-0x8294c form, so it is
   never taken, and the contract takes no UBSan premise for it. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import ExecF.
Open Scope Z_scope.

Definition DIGINET_PERSONALITY_OF : Z := 0x8513c.

(* The image-B address of personalities (symtab, and the auipc / addi at 0x82958 / 0x8295c). *)
Definition PERSONALITIES_B : Z := 0x9e240.

(* The C pointer of a DgnLib.v personality index at image B: &personalities[i], or NULL. *)
Definition personality_ptr_B (p : option Z) : Z :=
  match p with Some i => PERSONALITIES_B + 24 * i | None => 0 end.

Definition diginet_personality_of_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (desk : Z),
    0 <= desk < 2^64 ->
    ExecF.evtF tfibsegs RNG
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (personality_ptr_B (diginet_personality_of desk))) a1' a2' a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom tfibsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 desk) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_PERSONALITY_OF) fc None m (seg_rom tfibsegs)).
