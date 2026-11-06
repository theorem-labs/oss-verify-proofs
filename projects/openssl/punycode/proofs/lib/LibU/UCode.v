(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.punycode.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation USEGS := Ubsan.M.loaded_segments.

Definition C_strlen : code := Eval vm_compute in (mk_code USEGS 0x2bd350 36).
Lemma C_strlen_eq : mk_code USEGS 0x2bd350 36 = C_strlen.
Proof. vm_compute. reflexivity. Qed.

Definition C_strchrnul : code := Eval vm_compute in (mk_code USEGS 0x2bcfa0 56).
Lemma C_strchrnul_eq : mk_code USEGS 0x2bcfa0 56 = C_strchrnul.
Proof. vm_compute. reflexivity. Qed.

Definition C_strchr : code := Eval vm_compute in (mk_code USEGS 0x2bcf64 15).
Lemma C_strchr_eq : mk_code USEGS 0x2bcf64 15 = C_strchr.
Proof. vm_compute. reflexivity. Qed.

Definition C_strncmp : code := Eval vm_compute in (mk_code USEGS 0x2bd3e0 24).
Lemma C_strncmp_eq : mk_code USEGS 0x2bd3e0 24 = C_strncmp.
Proof. vm_compute. reflexivity. Qed.

Definition C_memcpy : code := Eval vm_compute in (mk_code USEGS 0x2bc8ec 257).
Lemma C_memcpy_eq : mk_code USEGS 0x2bc8ec 257 = C_memcpy.
Proof. vm_compute. reflexivity. Qed.

Definition C_memmove : code := Eval vm_compute in (mk_code USEGS 0x2bccf0 95).
Lemma C_memmove_eq : mk_code USEGS 0x2bccf0 95 = C_memmove.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_get_curr : code := Eval vm_compute in (mk_code USEGS 0x128aa0 37).
Lemma C_wp_get_curr_eq : mk_code USEGS 0x128aa0 37 = C_wp_get_curr.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_reserve : code := Eval vm_compute in (mk_code USEGS 0x128914 66).
Lemma C_wp_reserve_eq : mk_code USEGS 0x128914 66 = C_wp_reserve.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_alloc : code := Eval vm_compute in (mk_code USEGS 0x1288a8 27).
Lemma C_wp_alloc_eq : mk_code USEGS 0x1288a8 27 = C_wp_alloc.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_memcpy : code := Eval vm_compute in (mk_code USEGS 0x129374 31).
Lemma C_wp_memcpy_eq : mk_code USEGS 0x129374 31 = C_wp_memcpy.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_put_bytes : code := Eval vm_compute in (mk_code USEGS 0x1292a4 26).
Lemma C_wp_put_bytes_eq : mk_code USEGS 0x1292a4 26 = C_wp_put_bytes.
Proof. vm_compute. reflexivity. Qed.

Definition C_put_value : code := Eval vm_compute in (mk_code USEGS 0x12930c 26).
Lemma C_put_value_eq : mk_code USEGS 0x12930c 26 = C_put_value.
Proof. vm_compute. reflexivity. Qed.

Definition C_decode : code := Eval vm_compute in (mk_code USEGS 0x215490 255).
Lemma C_decode_eq : mk_code USEGS 0x215490 255 = C_decode.
Proof. vm_compute. reflexivity. Qed.

Definition C_a2ulabel : code := Eval vm_compute in (mk_code USEGS 0x21588c 213).
Lemma C_a2ulabel_eq : mk_code USEGS 0x21588c 213 = C_a2ulabel.
Proof. vm_compute. reflexivity. Qed.
