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
YB0z YE2g YF8z YF90 YF9g YB10 YE1y YE2b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO38 YE2r YE22 YE2t YE2l YE2s YE2y YE2d YE2k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE0s.
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
Definition FP_ENTRY : Z := 0x42100.
Definition FPI_STK : Z := 9216.
Definition hull_zero (rd : Z -> option Z) (x n : Z) : Prop := forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd s = Some 0.
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis TB : TraSyms B.
Hypothesis TL : TraSyms B.
Theorem tra_fprintf_icpt_usage : forall ly S (W : world trasegs) regs mem md ch s (str : list byte) L cval T,
ecall_pre trasegs B ly S W regs mem md ->
ly_stk_lo ly + FPI_STK <= spZ regs ->
(forall a, spZ regs - FPI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_usage -> getr regs 12 = w64 s ->
L = Z.of_nat (length str) -> L <= 33554425 ->
1 <= s -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= spZ regs - FPI_STK \/ spZ regs <= s) ->
(s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) -> amem_range s (L + 1) ->
vf_tail W mem s L -> mconsts_view W mem ->
vf_str W mem s str ->
range_addressable (aview trasegs (w_H W) mem) SHADOW_OFF s (L + 1) ->
shadow_hull_vis (aview trasegs (w_H W) mem) s (L + 1) ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem trasegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trasegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
hull_zero (aview trasegs (w_H W) mem) FMT_usage 17 ->
fdchan (Z_to_bv 64 2) ch md -> AI trasegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR trasegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 (L + 14) ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FPI_STK <= a < spZ regs) -> ~ vf_file a -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI trasegs (w_H W) (w_A W) md' ->
srealizes trasegs (cfg_at trasegs (raZ regs) regs' mem' md') T) ->
srealizes trasegs (cfg_at trasegs FP_ENTRY regs mem md)
(t_emit (map (WriteEv ch) (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2)) T).
Proof. first [ exact (YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) | exact ((YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) B LAWS TB TL) | exact ((YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) B LAWS TB) | exact ((YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) B LAWS TL) | exact ((YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) B TB TL) | exact ((YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) LAWS TB TL) | exact ((YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) B LAWS) | exact ((YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) B TB) | exact ((YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) LAWS TB) | exact ((YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) B TL) | exact ((YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) LAWS TL) | exact ((YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)) TB TL) | solve [ eapply (YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE0s.tfx_fprintf_icpt_usage (imgk := YF00.K_tra)); eassumption ] ]. Qed.
End c.
End b.
