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
Definition C_strlen : code := Eval vm_compute in (mk_code ASEGS 0x52ade8 36).
Lemma C_strlen_eq : mk_code ASEGS 0x52ade8 36 = C_strlen.
Proof. vm_compute. reflexivity. Qed.

Definition C_strchrnul : code := Eval vm_compute in (mk_code ASEGS 0x52aa20 57).
Lemma C_strchrnul_eq : mk_code ASEGS 0x52aa20 57 = C_strchrnul.
Proof. vm_compute. reflexivity. Qed.

Definition C_strchr : code := Eval vm_compute in (mk_code ASEGS 0x52a9e4 15).
Lemma C_strchr_eq : mk_code ASEGS 0x52a9e4 15 = C_strchr.
Proof. vm_compute. reflexivity. Qed.

Definition C_memcpy : code := Eval vm_compute in (mk_code ASEGS 0x52a4b8 257).
Lemma C_memcpy_eq : mk_code ASEGS 0x52a4b8 257 = C_memcpy.
Proof. vm_compute. reflexivity. Qed.

Definition C_tlsga : code := Eval vm_compute in (mk_code ASEGS 0x52b5a4 9).
Lemma C_tlsga_eq : mk_code ASEGS 0x52b5a4 9 = C_tlsga.
Proof. vm_compute. reflexivity. Qed.

Definition C_getspecific : code := Eval vm_compute in (mk_code ASEGS 0x52d410 7).
Lemma C_getspecific_eq : mk_code ASEGS 0x52d410 7 = C_getspecific.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_inited : code := Eval vm_compute in (mk_code ASEGS 0x1c9964 6).
Lemma C_inited_eq : mk_code ASEGS 0x1c9964 6 = C_inited.
Proof. vm_compute. reflexivity. Qed.

Definition C_tryinit : code := Eval vm_compute in (mk_code ASEGS 0x1ca874 40).
Lemma C_tryinit_eq : mk_code ASEGS 0x1ca874 40 = C_tryinit.
Proof. vm_compute. reflexivity. Qed.

Definition C_istrlen0 : code := Eval vm_compute in (mk_code ASEGS 0x1d503c 7).
Lemma C_istrlen0_eq : mk_code ASEGS 0x1d503c 7 = C_istrlen0.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_stubs : code := Eval vm_compute in (mk_code ASEGS 0x1ac5c4 36).
Lemma C_stubs_eq : mk_code ASEGS 0x1ac5c4 36 = C_stubs.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_ic_strlen : code := Eval vm_compute in (mk_code ASEGS 0x1ac6c4 165).
Lemma C_ic_strlen_eq : mk_code ASEGS 0x1ac6c4 165 = C_ic_strlen.
Proof. vm_compute. reflexivity. Qed.

Definition C_ic_strchr : code := Eval vm_compute in (mk_code ASEGS 0x1ad6fc 184).
Lemma C_ic_strchr_eq : mk_code ASEGS 0x1ad6fc 184 = C_ic_strchr.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_ic_strncmp : code := Eval vm_compute in (mk_code ASEGS 0x1ad120 375).
Lemma C_ic_strncmp_eq : mk_code ASEGS 0x1ad120 375 = C_ic_strncmp.
Proof. vm_compute. reflexivity. Qed.

Definition C_amemcpy : code := Eval vm_compute in (mk_code ASEGS 0x1c197c 295).
Lemma C_amemcpy_eq : mk_code ASEGS 0x1c197c 295 = C_amemcpy.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition C_malloc0 : code := Eval vm_compute in (mk_code ASEGS 0x1a6418 93).
Lemma C_malloc0_eq : mk_code ASEGS 0x1a6418 93 = C_malloc0.
Proof. vm_compute. reflexivity. Qed.

Definition C_ic_tlsga : code := Eval vm_compute in (mk_code ASEGS 0x1b3d90 31).
Lemma C_ic_tlsga_eq : mk_code ASEGS 0x1b3d90 31 = C_ic_tlsga.
Proof. vm_compute. reflexivity. Qed.

Definition C_curthread : code := Eval vm_compute in (mk_code ASEGS 0x1cd120 8).
Lemma C_curthread_eq : mk_code ASEGS 0x1cd120 8 = C_curthread.
Proof. vm_compute. reflexivity. Qed.

Definition C_tsdget : code := Eval vm_compute in (mk_code ASEGS 0x1c5718 17).
Lemma C_tsdget_eq : mk_code ASEGS 0x1c5718 17 = C_tsdget.
Proof. vm_compute. reflexivity. Qed.

Definition C_dtls : code := Eval vm_compute in (mk_code ASEGS 0x1dab78 212).
Lemma C_dtls_eq : mk_code ASEGS 0x1dab78 212 = C_dtls.
Proof. vm_compute. reflexivity. Qed.

Definition C_m2s : code := Eval vm_compute in (mk_code ASEGS 0x1a75f4 79).
Lemma C_m2s_eq : mk_code ASEGS 0x1a75f4 79 = C_m2s.
Proof. vm_compute. reflexivity. Qed.
