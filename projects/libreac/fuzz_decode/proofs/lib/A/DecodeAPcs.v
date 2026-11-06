(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_decode's ASan image: the two trampoline pcs the program's call rules are stated at
   (lib/A/DecodeClose.v HB_PC_WRAP_MALLOC / HB_PC_WRAP_FREE) equal the listing's sigma, at the core's concrete
   symbol record GrantB (lib/A/AD2l.v, code record lib/A/AF0l.v Tfib_code). Both sides are literals of the same
   image: __interceptor_trampoline_malloc = 0x51f64 and __interceptor_trampoline_free = 0x51f60 in
   fuzz_decode.asan's symbol table (internal path). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AD2l.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr.

Lemma decA_pc_wrap_malloc : pc_wrap_malloc (as_code GrantB) = decode_sigma DS___interceptor_trampoline_malloc.
Proof. reflexivity. Qed.

Lemma decA_pc_wrap_free : pc_wrap_free (as_code GrantB) = decode_sigma DS___interceptor_trampoline_free.
Proof. reflexivity. Qed.

Print Assumptions decA_pc_wrap_malloc.
Print Assumptions decA_pc_wrap_free.
