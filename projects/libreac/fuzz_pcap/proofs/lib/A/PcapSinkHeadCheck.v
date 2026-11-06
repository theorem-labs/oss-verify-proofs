From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap: it checks lib/Reusable/PcapSinkHeads.v's
   two ofl_head addresses against the code of the two ASan images. In each image musl's __ofl_lock forms the
   address of ofl_lock with an auipc + addi pair and returns ofl_lock + 8 = &ofl_head (`addi a0, s0, 8`), which
   __ofl_add then loads (`ld a1, 0(a0)`). No auipc pair in either image forms ofl_head directly, and no data
   word holds it. The three words are read from each image's loaded segments, decoded, and their immediates
   summed:
     fuzz_pcap.asan       __ofl_lock 0x8f1dc: 0x8f1e8 auipc a0,0x566; 0x8f1ec addi s0,a0,-0x268;
                          0x8f1f8 addi a0,s0,8 -> 0x5f4f80 + 8 = 0x5f4f88
     fuzz_pcap.asan-ubsan __ofl_lock 0x8f0a8: 0x8f0b4 auipc a0,0x566; 0x8f0b8 addi s0,a0,-0x234;
                          0x8f0c4 addi a0,s0,8 -> 0x5f4e80 + 8 = 0x5f4e88
   (symbols ofl_lock / ofl_head / __ofl_lock / __ofl_add from the unstripped twins; code equal to the pins). *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.libreac.fuzz_pcap.images Require Asan AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YI16 PcapSinkHeads.
Local Open Scope Z_scope.
Local Ltac div_vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* fuzz_pcap.asan *)
Definition asan_ofl_hi : bv 20 := Z_to_bv 20 0x566.
Definition asan_ofl_lo : bv 12 := Z_to_bv 12 (-0x268).
Definition ofl_head_off : bv 12 := Z_to_bv 12 8.

Theorem asan_ofl_words :
  fetch_word Asan.M.loaded_segments (Z_to_bv 64 (symaddr (Symbols.Asan.s___ofl_lock + 0xc)%Z)) = Some (Z_to_bv 32 0x00566517) /\
  fetch_word Asan.M.loaded_segments (Z_to_bv 64 (symaddr (Symbols.Asan.s___ofl_lock + 0x10)%Z)) = Some (Z_to_bv 32 0xd9850413) /\
  fetch_word Asan.M.loaded_segments (Z_to_bv 64 (symaddr (Symbols.Asan.s___ofl_lock + 0x1c)%Z)) = Some (Z_to_bv 32 0x00840513).
Proof. split; [div_vm_refl | split; div_vm_refl]. Qed.

Theorem asan_ofl_decode :
  decode_any (Z_to_bv 32 0x00566517) = Some (Auipc 10 asan_ofl_hi, 4) /\
  decode_any (Z_to_bv 32 0xd9850413) = Some (OpImm ALU_ADD 8 10 asan_ofl_lo, 4) /\
  decode_any (Z_to_bv 32 0x00840513) = Some (OpImm ALU_ADD 10 8 ofl_head_off, 4).
Proof. split; [div_vm_refl | split; div_vm_refl]. Qed.

Theorem asan_ofl_head_addr :
  (symaddr (Symbols.Asan.s___ofl_lock + 0xc)%Z) + Z.shiftl (bv_signed asan_ofl_hi) 12 + bv_signed asan_ofl_lo + bv_signed ofl_head_off
  = @YI16.sk_ofl_head PcapSinkHeads.asan_sink_head.
Proof. vm_compute. reflexivity. Qed.

(* fuzz_pcap.asan-ubsan *)
Definition asan_ubsan_ofl_hi : bv 20 := Z_to_bv 20 0x566.
Definition asan_ubsan_ofl_lo : bv 12 := Z_to_bv 12 (-0x234).

Theorem asan_ubsan_ofl_words :
  fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 (symaddr (Symbols.AsanUbsan.s___ofl_lock + 0xc)%Z)) = Some (Z_to_bv 32 0x00566517) /\
  fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 (symaddr (Symbols.AsanUbsan.s___ofl_lock + 0x10)%Z)) = Some (Z_to_bv 32 0xdcc50413) /\
  fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 (symaddr (Symbols.AsanUbsan.s___ofl_lock + 0x1c)%Z)) = Some (Z_to_bv 32 0x00840513).
Proof. split; [div_vm_refl | split; div_vm_refl]. Qed.

Theorem asan_ubsan_ofl_decode :
  decode_any (Z_to_bv 32 0x00566517) = Some (Auipc 10 asan_ubsan_ofl_hi, 4) /\
  decode_any (Z_to_bv 32 0xdcc50413) = Some (OpImm ALU_ADD 8 10 asan_ubsan_ofl_lo, 4) /\
  decode_any (Z_to_bv 32 0x00840513) = Some (OpImm ALU_ADD 10 8 ofl_head_off, 4).
Proof. split; [div_vm_refl | split; div_vm_refl]. Qed.

Theorem asan_ubsan_ofl_head_addr :
  (symaddr (Symbols.Asan.s___fwritex + 0x11c)%Z) + Z.shiftl (bv_signed asan_ubsan_ofl_hi) 12 + bv_signed asan_ubsan_ofl_lo + bv_signed ofl_head_off
  = @YI16.sk_ofl_head PcapSinkHeads.asan_ubsan_sink_head.
Proof. vm_compute. reflexivity. Qed.
