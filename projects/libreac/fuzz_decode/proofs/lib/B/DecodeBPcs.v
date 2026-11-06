(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_decode's ASan+UBSan image, the image-B twin of
   lib/A/DecodeAPcs.v (a working branch 8229e64eeee): the two trampoline pcs the program's call rules
   are stated at (lib/B/DecodeBClose.v :312 HB_PC_WRAP_MALLOC / :313 HB_PC_WRAP_FREE) equal the listing's sigma, at
   the core's concrete symbol record TfibB (lib/B/YD2l.v, code record lib/B/YF0l.v Tfib_code). Both sides are
   literals of the same image: __interceptor_trampoline_malloc = 0x51fb0 and __interceptor_trampoline_free = 0x51fac
   in fuzz_decode.asan-ubsan's symbol table (each a 4-byte `j`, to ___interceptor_malloc 0x52188 and
   ___interceptor_free 0x51fb8). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YD2l.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr.

Lemma decB_pc_wrap_malloc : pc_wrap_malloc (as_code TfibB) = decodeb_sigma DB___interceptor_trampoline_malloc.
Proof. reflexivity. Qed.

Lemma decB_pc_wrap_free : pc_wrap_free (as_code TfibB) = decodeb_sigma DB___interceptor_trampoline_free.
Proof. reflexivity. Qed.

Print Assumptions decB_pc_wrap_malloc.
Print Assumptions decB_pc_wrap_free.
