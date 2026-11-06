(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.punycode.images Require Import Plain.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation PSEGS := Plain.M.loaded_segments.

Definition C_strlen : code := Eval vm_compute in (mk_code PSEGS 0x276ea8 36).
Lemma C_strlen_eq : mk_code PSEGS 0x276ea8 36 = C_strlen.
Proof. vm_compute. reflexivity. Qed.

Definition C_strchrnul : code := Eval vm_compute in (mk_code PSEGS 0x276af8 56).
Lemma C_strchrnul_eq : mk_code PSEGS 0x276af8 56 = C_strchrnul.
Proof. vm_compute. reflexivity. Qed.

Definition C_strchr : code := Eval vm_compute in (mk_code PSEGS 0x276abc 15).
Lemma C_strchr_eq : mk_code PSEGS 0x276abc 15 = C_strchr.
Proof. vm_compute. reflexivity. Qed.

Definition C_strncmp : code := Eval vm_compute in (mk_code PSEGS 0x276f38 24).
Lemma C_strncmp_eq : mk_code PSEGS 0x276f38 24 = C_strncmp.
Proof. vm_compute. reflexivity. Qed.

Definition C_memcpy : code := Eval vm_compute in (mk_code PSEGS 0x276444 257).
Lemma C_memcpy_eq : mk_code PSEGS 0x276444 257 = C_memcpy.
Proof. vm_compute. reflexivity. Qed.

Definition C_memmove : code := Eval vm_compute in (mk_code PSEGS 0x276848 95).
Lemma C_memmove_eq : mk_code PSEGS 0x276848 95 = C_memmove.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_get_curr : code := Eval vm_compute in (mk_code PSEGS 0x119eb4 26).
Lemma C_wp_get_curr_eq : mk_code PSEGS 0x119eb4 26 = C_wp_get_curr.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_reserve : code := Eval vm_compute in (mk_code PSEGS 0x119d64 57).
Lemma C_wp_reserve_eq : mk_code PSEGS 0x119d64 57 = C_wp_reserve.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_memcpy : code := Eval vm_compute in (mk_code PSEGS 0x11a718 40).
Lemma C_wp_memcpy_eq : mk_code PSEGS 0x11a718 40 = C_wp_memcpy.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_put_bytes : code := Eval vm_compute in (mk_code PSEGS 0x11a66c 43).
Lemma C_wp_put_bytes_eq : mk_code PSEGS 0x11a66c 43 = C_wp_put_bytes.
Proof. vm_compute. reflexivity. Qed.

Definition C_decode : code := Eval vm_compute in (mk_code PSEGS 0x1e0688 204).
Lemma C_decode_eq : mk_code PSEGS 0x1e0688 204 = C_decode.
Proof. vm_compute. reflexivity. Qed.

Definition C_a2ulabel : code := Eval vm_compute in (mk_code PSEGS 0x1e09b8 168).
Lemma C_a2ulabel_eq : mk_code PSEGS 0x1e09b8 168 = C_a2ulabel.
Proof. vm_compute. reflexivity. Qed.
