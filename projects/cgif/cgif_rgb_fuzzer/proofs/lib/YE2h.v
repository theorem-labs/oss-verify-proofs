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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO38 YE2r YE22 YE2t YE2s YE2x.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE1k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition VP_ENTRY : Z := 0x420f4.
Definition VP_RET2 : Z := 0x4558c.
Definition VP_RET1 : Z := 0x44a1c.
Definition VP_WIN : Z := 2432.
Definition VPI_STK : Z := 9200.
Definition FMT : Z := 0x14861.
Definition hull_zero (rd : Z -> option Z) (x n : Z) : Prop := forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd s = Some 0.
Definition KEPTA : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition vpf_saved (regs : bvmap 5 word) (m : word -> option byte) (sp0 : Z) : Prop :=
val_mem trasegs m (sp0 - 8) 8 (bv_unsigned (getr regs 1)) /\ val_mem trasegs m (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem trasegs m (sp0 - 24) 8 (bv_unsigned (getr regs 9)) /\ val_mem trasegs m (sp0 - 80) 8 (bv_unsigned (getr regs 18)) /\
val_mem trasegs m (sp0 - 72) 8 (sp0 + 24) /\ val_mem trasegs m (sp0 - 64) 8 FMT /\ val_mem trasegs m (sp0 - 56) 8 VP_RET1.
Lemma vpf_saved_kept : forall regs (H : word -> bool) (m m' : word -> option byte) sp0,
vpf_saved regs (mrestrict H m) sp0 -> (forall b, sp0 - 96 <= b < sp0 -> aview trasegs H m' b = aview trasegs H m b) ->
vpf_saved regs (mrestrict H m') sp0.
Proof. first [ exact (YE1k.vpf_saved_kept (imgk := YF00.K_tra)) | solve [ eapply (YE1k.vpf_saved_kept (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE1k.vpf_saved_kept (imgk := YF00.K_tra)); eassumption ] ]. Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis TB : TraSyms B.
Theorem tra_vprintf_icpt_A : forall ly S (W : world trasegs) regs mem md T,
ecall_pre trasegs B ly S W regs mem md ->
ly_stk_lo ly + VPI_STK <= spZ regs ->
(forall a, spZ regs - VPI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
spZ regs + 32 <= 2 ^ 47 ->
getr regs 10 = w64 FMT -> getr regs 11 = w64 (spZ regs + 24) ->
val_mem trasegs (mrestrict (w_H W) mem) (spZ regs + 24) 8 0 ->
ro_img (mrestrict (w_H W) mem) ->
hull_zero (aview trasegs (w_H W) mem) FMT 4 ->
AI trasegs (w_H W) (w_A W) md ->
(forall regs1 mem1 md1,
ecall_pre trasegs B ly S W regs1 mem1 md1 ->
spZ regs1 = spZ regs - 96 -> raZ regs1 = VP_RET2 ->
getr regs1 10 = w64 F_STDOUT -> getr regs1 11 = w64 FMT -> getr regs1 12 = w64 (spZ regs + 24) ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
(forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr regs1 r = getr regs r) ->
same_but_materialized md md1 ->
(forall z : word, ~ (spZ regs - VP_WIN <= bv_unsigned z < spZ regs) -> mem1 z = mem z) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - VP_WIN <= a < spZ regs) -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
vpf_saved regs (mrestrict (w_H W) mem1) (spZ regs) ->
AI trasegs (w_H W) (w_A W) md1 ->
srealizes trasegs (cfg_at trasegs A_vfprintf regs1 mem1 md1) T) ->
srealizes trasegs (cfg_at trasegs VP_ENTRY regs mem md) T.
Proof. first [ exact (YE1k.tfx_vprintf_icpt_A (imgk := YF00.K_tra)) | exact ((YE1k.tfx_vprintf_icpt_A (imgk := YF00.K_tra)) B LAWS TB) | exact ((YE1k.tfx_vprintf_icpt_A (imgk := YF00.K_tra)) B LAWS) | exact ((YE1k.tfx_vprintf_icpt_A (imgk := YF00.K_tra)) B TB) | exact ((YE1k.tfx_vprintf_icpt_A (imgk := YF00.K_tra)) LAWS TB) | exact ((YE1k.tfx_vprintf_icpt_A (imgk := YF00.K_tra)) B) | exact ((YE1k.tfx_vprintf_icpt_A (imgk := YF00.K_tra)) LAWS) | exact ((YE1k.tfx_vprintf_icpt_A (imgk := YF00.K_tra)) TB) | solve [ eapply (YE1k.tfx_vprintf_icpt_A (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE1k.tfx_vprintf_icpt_A (imgk := YF00.K_tra)); eassumption ] ]. Qed.
Theorem tra_vprintf_icpt_E : forall (W : world trasegs) (regs regs2 : bvmap 5 word) mem2 md2 (T : TSet),
2 ^ 44 <= spZ regs -> spZ regs + 32 <= 2 ^ 47 -> spZ regs mod 16 = 0 -> YK0s.ret_ok (getr regs 1) ->
getr regs2 2 = w64 (spZ regs - 96) ->
vpf_saved regs (mrestrict (w_H W) mem2) (spZ regs) ->
AI trasegs (w_H W) (w_A W) md2 ->
(forall regs3 mem3 md3,
(forall z, mem3 z = mem2 z) ->
getr regs3 2 = getr regs 2 -> getr regs3 1 = getr regs 1 -> getr regs3 8 = getr regs 8 -> getr regs3 9 = getr regs 9 -> getr regs3 18 = getr regs 18 ->
(forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31] ->
getr regs3 r = getr regs2 r) ->
same_but_materialized md2 md3 -> AI trasegs (w_H W) (w_A W) md3 ->
srealizes trasegs (cfg_at trasegs (raZ regs) regs3 mem3 md3) T) ->
srealizes trasegs (cfg_at trasegs VP_RET2 regs2 mem2 md2) T.
Proof. first [ exact (YE1k.tfx_vprintf_icpt_E (imgk := YF00.K_tra)) | exact ((YE1k.tfx_vprintf_icpt_E (imgk := YF00.K_tra)) B LAWS TB) | exact ((YE1k.tfx_vprintf_icpt_E (imgk := YF00.K_tra)) B LAWS) | exact ((YE1k.tfx_vprintf_icpt_E (imgk := YF00.K_tra)) B TB) | exact ((YE1k.tfx_vprintf_icpt_E (imgk := YF00.K_tra)) LAWS TB) | exact ((YE1k.tfx_vprintf_icpt_E (imgk := YF00.K_tra)) B) | exact ((YE1k.tfx_vprintf_icpt_E (imgk := YF00.K_tra)) LAWS) | exact ((YE1k.tfx_vprintf_icpt_E (imgk := YF00.K_tra)) TB) | solve [ eapply (YE1k.tfx_vprintf_icpt_E (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE1k.tfx_vprintf_icpt_E (imgk := YF00.K_tra)); eassumption ] ]. Qed.
End d.
End c.
