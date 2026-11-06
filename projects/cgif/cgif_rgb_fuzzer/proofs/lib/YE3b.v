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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE3s YE33.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE0u.
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
Definition FW_ENTRY : Z := 0x423ac.
Definition FWI_STK : Z := 6224.
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis TB : TrbSyms B.
Theorem trb_fwrite_icpt : forall ly S (W : world trbsegs) regs mem md ch p size cval (msg : list byte) T,
ecall_pre trbsegs B ly S W regs mem md ->
ly_stk_lo ly + FWI_STK <= spZ regs ->
(forall a, spZ regs - FWI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 p -> getr regs 11 = w64 size -> getr regs 12 = w64 1 -> getr regs 13 = w64 F_STDERR ->
1 <= size -> size <= 2 ^ 25 ->
0 <= p -> p + size <= kHighMemEnd ->
(p + size <= spZ regs - FWI_STK \/ spZ regs <= p) ->
(p + size <= F_STDERR \/ F_STDERR + FILE_SZ <= p) ->
rdn trbsegs (mrestrict (w_H W) mem) (Z_to_bv 64 p) (Z.to_nat size) = Some msg ->
stderr_pristine (mrestrict (w_H W) mem) ->
(forall a, F_STDERR <= a < F_STDERR + FILE_SZ -> ~ aowned B ly S a) ->
val_mem trbsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trbsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
amem_range p size ->
range_addressable (aview trbsegs (w_H W) mem) SHADOW_OFF p size ->
shadow_hull_vis (aview trbsegs (w_H W) mem) p size ->
fdchan (Z_to_bv 64 2) ch md -> AI trbsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR trbsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 1 ->
stderr_written (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FWI_STK <= a < spZ regs) -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) ->
aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI trbsegs (w_H W) (w_A W) md' ->
srealizes trbsegs (cfg_at trbsegs (raZ regs) regs' mem' md') T) ->
srealizes trbsegs (cfg_at trbsegs FW_ENTRY regs mem md) (t_emit (map (WriteEv ch) msg) T).
Proof. first [ exact (YE0u.tfx_fwrite_icpt (imgk := YF00.K_trb)) | exact ((YE0u.tfx_fwrite_icpt (imgk := YF00.K_trb)) B LAWS TB) | exact ((YE0u.tfx_fwrite_icpt (imgk := YF00.K_trb)) B LAWS) | exact ((YE0u.tfx_fwrite_icpt (imgk := YF00.K_trb)) B TB) | exact ((YE0u.tfx_fwrite_icpt (imgk := YF00.K_trb)) LAWS TB) | exact ((YE0u.tfx_fwrite_icpt (imgk := YF00.K_trb)) B) | exact ((YE0u.tfx_fwrite_icpt (imgk := YF00.K_trb)) LAWS) | exact ((YE0u.tfx_fwrite_icpt (imgk := YF00.K_trb)) TB) | solve [ eapply (YE0u.tfx_fwrite_icpt (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE0u.tfx_fwrite_icpt (imgk := YF00.K_trb)); eassumption ] ]. Qed.
End c.
End b.
