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
YB1u YE3h YF9i YF9j YFa1 YB1v YE2z YE3c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE1g.
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
Theorem aread_check_realizes : forall B, AR_laws trbsegs B -> TrbSyms B ->
forall ly S (W : world trbsegs) regs mem md n p,
ecall_pre trbsegs B ly S W regs mem md ->
getr regs 10 = w64 n -> getr regs 9 = w64 p -> 0 < n < 2 ^ 31 -> 0 <= p -> p + n <= 2 ^ 63 ->
amem_range p n -> range_addressable (aview trbsegs (w_H W) mem) SHADOW_OFF p n -> shadow_hull_vis (aview trbsegs (w_H W) mem) p n ->
SRr trbsegs W (cfg_at trbsegs 0x4410c regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at trbsegs 0x44164 regs' mem' md' /\
AR trbsegs B ly S W mem' md' /\
(forall r, acallee_saved r -> r <> 9 -> r <> 18 -> r <> 20 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
same_but_materialized md md' /\
getr regs' 10 = w64 n /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof. first [ exact (YE1g.aread_check_realizes (imgk := YF00.K_trb)) | solve [ eapply (YE1g.aread_check_realizes (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE1g.aread_check_realizes (imgk := YF00.K_trb)); eassumption ] ]. Qed.
End b.
