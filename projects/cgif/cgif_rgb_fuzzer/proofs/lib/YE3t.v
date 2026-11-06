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
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB1u YE3h YF9i YF9j YE3r YE3s YE3m YE33 YE3u YE31 YFa1 YE2z YE3c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE1r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition A_vfprintf : Z := 0x98db8.
Definition VF_STK : Z := 912 + 2 * ESTACK.
Definition xret_realizes (segs : list Segment) (B : asyms) (pc : Z) (xw : Z -> Prop)
(xpre : world segs -> (word -> option byte) -> Prop) : Prop :=
forall ly S (W : world segs) regs mem md,
ecall_pre segs B ly S W regs mem md -> xpre W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> ~ aowned B ly S a -> ~ xw a ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ xw a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition xret_realizes_noar (segs : list Segment) (B : asyms) (pc : Z) (xw : Z -> Prop)
(xpre : world segs -> (word -> option byte) -> Prop) : Prop :=
forall ly S (W : world segs) regs mem md,
ecall_pre segs B ly S W regs mem md -> xpre W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> ~ xw a ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ xw a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition vf_str (W : world trbsegs) (mem : word -> option byte) (s : Z) (str : list byte) : Prop :=
(forall i, (i < length str)%nat -> aview trbsegs (w_H W) mem (s + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))) /\
aview trbsegs (w_H W) mem (s + Z.of_nat (length str)) = Some 0 /\
Forall (fun b : byte => bv_unsigned b <> 0) str.
Definition vf_band (sp0 a : Z) : Prop := sp0 - VF_STK <= a < sp0.
Definition vf_file (a : Z) : Prop := F_STDERR <= a < F_STDERR + FILE_SZ.
Definition vf_tail (W : world trbsegs) (mem : word -> option byte) (s L : Z) : Prop :=
forall a, s + L < a < s + L - (s + L) mod 8 + 8 -> aview trbsegs (w_H W) mem a <> None.
Lemma trb_rom_low : forall a, in_rom trbsegs a -> 0 <= a < 0xa2000.
Proof. first [ exact (YE1r.tfx_rom_low (imgk := YF00.K_trb)) | solve [ eapply (YE1r.tfx_rom_low (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE1r.tfx_rom_low (imgk := YF00.K_trb)); eassumption ] ]. Qed.
Definition stderr_fields_after_vf : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, 0x97e88); (32, 8%N, 0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0); (64, 8%N, 0);
(72, 8%N, 0x97fd4); (80, 8%N, 0x97fcc); (88, 8%N, STDERR_BUF); (96, 8%N, 0); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 2);
(128, 8%N, 0); (136, 4%N, 0xffffffff); (140, 4%N, 0xffffffff); (144, 8%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition stderr_after_vfprintf : (word -> option byte) -> Prop := file_is stderr_fields_after_vf.
End c.
