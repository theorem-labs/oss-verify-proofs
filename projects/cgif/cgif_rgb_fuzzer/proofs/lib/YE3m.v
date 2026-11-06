(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YB1v YE3n.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE1n.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition MC_LO : Z := trb_D_const_HIGHS_0x8080808080808080.
Definition MC_HI : Z := trb_D_const_ONES_0x0101010101010100 + 8.
Definition mconsts_view (W : world trbsegs) (mem : word -> option byte) : Prop :=
forall a, MC_LO <= a < MC_HI -> aview trbsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom trbsegs (Z_to_bv 64 a)).
Lemma mc_bounds : MC_LO = 0x10370 /\ MC_HI = 0x10390.
Proof. first [ exact (YE1n.mc_bounds (imgk := YF00.K_trb)) | solve [ eapply (YE1n.mc_bounds (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE1n.mc_bounds (imgk := YF00.K_trb)); eassumption ] ]. Qed.
End c.
