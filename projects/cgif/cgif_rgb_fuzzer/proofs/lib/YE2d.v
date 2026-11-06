(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k YK1d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YA0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB0z YE2g YF8z YF90 YF9g YB10 YE2o YE1y YE2b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Theorem memcpy_icpt_realizes : forall B, AR_laws trasegs B -> TraSyms B ->
forall ly S (W : world trasegs) regs mem md d x n,
ecall_pre trasegs B ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok trasegs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview trasegs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview trasegs (w_H W) mem) d n) ->
(0 <= x /\ x + n <= 2 ^ 63 /\ src_ok trasegs W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview trasegs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview trasegs (w_H W) mem) x n)) ->
SRr trasegs W (cfg_at trasegs 0x51dac regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at trasegs (raZ regs) regs' mem' md' /\
AR trasegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview trasegs (w_H W) mem' (d + i) = aview trasegs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof. first [ exact (YE16.memcpy_icpt_realizes (imgk := YF00.K_tra)) | solve [ eapply (YE16.memcpy_icpt_realizes (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE16.memcpy_icpt_realizes (imgk := YF00.K_tra)); eassumption ] ]. Qed.
End b.
