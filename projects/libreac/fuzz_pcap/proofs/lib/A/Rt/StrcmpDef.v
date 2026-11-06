From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10 (a Theorem Labs lane), for libreac/fuzz_pcap's v1.9.0 ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t YCe5.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y AE3i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN32 YG0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* The strcmp interceptor of libreac/fuzz_pcap's v1.9.0 ASan build, in cgif_file's interceptor-contract vocabulary
   (YG0d.v ecall_pre / aregs_preserved / same_but_materialized, as abcmp_realizes and amemcmp_realizes state theirs;
   literal-instance form as A/AE2j.v's tfib_strchr_lit). The proof is A/Rt/StrcmpIcpt.v.
   Call site (the one in the reach, MEASURED on fuzz_pcap.asan v1.9.0): libreac_fuzz_fopen, jal 0x41564 at 0x80760
   (ra = 0x80764); a0 = a1 = 0x20d00, the rodata literal "<fuzz-input>" (12 bytes + NUL).
   Code: trampoline 0x41564 (j 0x41b28) -> ___interceptor_strcmp 0x41b28 (1328 B, 332 insns), returns at 0x41cc0.
   Its frame is 0x7f0 at 0x41b28 (plus 0xa0 at 0x41b64); the deepest stack on the premises' path, callees included,
   is 2208 bytes (auditor, 21:14Z), inside ecall_pre's ESTACK = 4096 window, which is the only window this states. *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition SM_ENTRY : Z := (symaddr Symbols.Asan.s___wrap_strcmp).
Definition A_FUZZ_PATH : Z := (symaddr (Symbols.Asan.Sec.s_rodata + 68128)%Z).
(* "<fuzz-input>" *)
Definition FUZZ_PATH_BYTES : list Z := [60; 102; 117; 122; 122; 45; 105; 110; 112; 117; 116; 62].
(* The literal instances of the reach: (a0, a1, result). *)
Definition SM_INST : list (Z * Z * Z) := [(A_FUZZ_PATH, A_FUZZ_PATH, 0)].
Variable B : asyms.
Definition astrcmp_post (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (res : Z) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
  getr regs' 10 = w64 res /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
(* The contract: at a literal instance (x, y, res) of SM_INST, both strings in the read-only image, their bytes and
   the NUL addressable in ASan's shadow, strcmp returns res (0 for equal strings), keeps memory outside its own stack
   window, the ASan state AR, the callee-saved registers, and makes no event. *)
Definition astrcmp_lit_realizes : Prop :=
  forall x y res, In (x, y, res) SM_INST ->
  forall ly S W regs mem md,
  ecall_pre tfibsegs B ly S W regs mem md ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y ->
  ro_img (mrestrict (w_H W) mem) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length FUZZ_PATH_BYTES) + 1) ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) x (Z.of_nat (length FUZZ_PATH_BYTES) + 1) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF y (Z.of_nat (length FUZZ_PATH_BYTES) + 1) ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) y (Z.of_nat (length FUZZ_PATH_BYTES) + 1) ->
  SRr tfibsegs W (cfg_at tfibsegs SM_ENTRY regs mem md) (astrcmp_post ly S W regs mem md res).
End s.
