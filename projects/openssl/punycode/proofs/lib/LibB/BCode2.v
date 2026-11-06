(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition C_wp_get_curr : code := Eval vm_compute in (mk_code BSEGS 0x2723cc 87).
Lemma C_wp_get_curr_eq : mk_code BSEGS 0x2723cc 87 = C_wp_get_curr.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_reserve : code := Eval vm_compute in (mk_code BSEGS 0x272128 120).
Lemma C_wp_reserve_eq : mk_code BSEGS 0x272128 120 = C_wp_reserve.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_alloc : code := Eval vm_compute in (mk_code BSEGS 0x272074 45).
Lemma C_wp_alloc_eq : mk_code BSEGS 0x272074 45 = C_wp_alloc.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_memcpy : code := Eval vm_compute in (mk_code BSEGS 0x273870 118).
Lemma C_wp_memcpy_eq : mk_code BSEGS 0x273870 118 = C_wp_memcpy.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_put_bytes : code := Eval vm_compute in (mk_code BSEGS 0x273608 114).
Lemma C_wp_put_bytes_eq : mk_code BSEGS 0x273608 114 = C_wp_put_bytes.
Proof. vm_compute. reflexivity. Qed.

Definition C_put_value : code := Eval vm_compute in (mk_code BSEGS 0x2737d0 40).
Lemma C_put_value_eq : mk_code BSEGS 0x2737d0 40 = C_put_value.
Proof. vm_compute. reflexivity. Qed.

Definition C_wp_init : code := Eval vm_compute in (mk_code BSEGS 0x272638 188).
Lemma C_wp_init_eq : mk_code BSEGS 0x272638 188 = C_wp_init.
Proof. vm_compute. reflexivity. Qed.

Definition C_a2ulabel : code := Eval vm_compute in (mk_code BSEGS 0x4312f4 376).
Lemma C_a2ulabel_eq : mk_code BSEGS 0x4312f4 376 = C_a2ulabel.
Proof. vm_compute. reflexivity. Qed.
