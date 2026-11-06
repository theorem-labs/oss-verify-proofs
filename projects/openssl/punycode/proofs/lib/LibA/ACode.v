(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.punycode.images Require Import Asan.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition C_imemmove : code := Eval vm_compute in (mk_code ASEGS 0x1d4e90 22).
Lemma C_imemmove_eq : mk_code ASEGS 0x1d4e90 22 = C_imemmove.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_memiszero : code := Eval vm_compute in (mk_code ASEGS 0x1d5418 45).
Lemma C_memiszero_eq : mk_code ASEGS 0x1d5418 45 = C_memiszero.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_memtoshadow : code := Eval vm_compute in (mk_code ASEGS 0x1c4aa8 79).
Lemma C_memtoshadow_eq : mk_code ASEGS 0x1c4aa8 79 = C_memtoshadow.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_regpoisoned : code := Eval vm_compute in (mk_code ASEGS 0x1c4f34 209).
Lemma C_regpoisoned_eq : mk_code ASEGS 0x1c4f34 209 = C_regpoisoned.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_amemmove : code := Eval vm_compute in (mk_code ASEGS 0x1c2058 220).
Lemma C_amemmove_eq : mk_code ASEGS 0x1c2058 220 = C_amemmove.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_decode : code := Eval vm_compute in (mk_code ASEGS 0x407b38 291).
Lemma C_decode_eq : mk_code ASEGS 0x407b38 291 = C_decode.
Proof. vm_compute. reflexivity. Qed.
