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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO38 YE3s YE33 YE3u YE3t YE3x YE3e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE0r.
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
Definition FP_ENTRY : Z := 0x423c4.
Definition FPI_STK : Z := 9216.
Definition hull_zero (rd : Z -> option Z) (x n : Z) : Prop := forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd s = Some 0.
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis TB : TrbSyms B.
Hypothesis TL : TrbSyms B.
Theorem trb_fprintf_icpt_refused : forall ly S (W : world trbsegs) regs mem md ch cval T,
ecall_pre trbsegs B ly S W regs mem md ->
ly_stk_lo ly + FPI_STK <= spZ regs ->
(forall a, spZ regs - FPI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_refused -> getr regs 12 = w64 V_refused ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem trbsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trbsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
hull_zero (aview trbsegs (w_H W) mem) FMT_refused 33 ->
fdchan (Z_to_bv 64 2) ch md -> AI trbsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR trbsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 38 ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FPI_STK <= a < spZ regs) -> ~ vf_file a -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI trbsegs (w_H W) (w_A W) md' ->
srealizes trbsegs (cfg_at trbsegs (raZ regs) regs' mem' md') T) ->
srealizes trbsegs (cfg_at trbsegs FP_ENTRY regs mem md) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) msg_refused)) T).
Proof. first [ exact (YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) | exact ((YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) B LAWS TB TL) | exact ((YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) B LAWS TB) | exact ((YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) B LAWS TL) | exact ((YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) B TB TL) | exact ((YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) LAWS TB TL) | exact ((YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) B LAWS) | exact ((YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) B TB) | exact ((YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) LAWS TB) | exact ((YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) B TL) | exact ((YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) LAWS TL) | exact ((YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)) TB TL) | solve [ eapply (YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE0r.tfx_fprintf_icpt_refused (imgk := YF00.K_trb)); eassumption ] ]. Qed.
End c.
End b.
