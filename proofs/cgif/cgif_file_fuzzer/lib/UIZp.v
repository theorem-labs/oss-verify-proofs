(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04 YI06 YI09 YI08.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma clz_xor_m1 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite lxor_allones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma clz_not_alias : forall E n m x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> ew E m = Z_to_bv 64 (2 ^ 64 - 1 - x) ->
sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = sv_denot E (SOff m 0).
Proof.
intros E n m x Hn Hx Hm. cbn [sv_denot]. rewrite Hn, Hm, !unsigned_lit_small by lia. rewrite !Z.add_0_r.
rewrite clz_xor_m1 by lia. reflexivity.
Qed.
