(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.punycode.images Require Import Asan.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import ACode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition C_wp_get_curr : code := Eval vm_compute in (mk_code ASEGS 0x26d560 77).
Lemma C_wp_get_curr_eq : mk_code ASEGS 0x26d560 77 = C_wp_get_curr.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_wp_reserve : code := Eval vm_compute in (mk_code ASEGS 0x26d2fc 110).
Lemma C_wp_reserve_eq : mk_code ASEGS 0x26d2fc 110 = C_wp_reserve.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_wp_memcpy : code := Eval vm_compute in (mk_code ASEGS 0x26ea98 139).
Lemma C_wp_memcpy_eq : mk_code ASEGS 0x26ea98 139 = C_wp_memcpy.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_wp_put_bytes : code := Eval vm_compute in (mk_code ASEGS 0x26e830 154).
Lemma C_wp_put_bytes_eq : mk_code ASEGS 0x26e830 154 = C_wp_put_bytes.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_a2ulabel : code := Eval vm_compute in (mk_code ASEGS 0x407fc4 355).
Lemma C_a2ulabel_eq : mk_code ASEGS 0x407fc4 355 = C_a2ulabel.
Proof. vm_compute. reflexivity. Qed.
