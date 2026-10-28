(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout F_memset.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition g_got_real_memset : Z := 0x5a9258.   (* [comment removed for export] *)
Definition g_real_memset : Z := 0x5ac4b0.       (* [comment removed for export] *)
Definition musl_memset_entry : Z := 0x52b4e0.

(* [comment removed for export] *)
Definition setshadow_cells (m : mem) : Prop :=
  rw_cells ctasegs m g_got_real_memset [C8 (Z_to_bv 64 g_real_memset)]
  /\ rw_cells ctasegs m g_real_memset [C8 (Z_to_bv 64 musl_memset_entry)].

Definition set_shadow_stmt (entry v : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (sa n : Z) (junk : list byte),
  a0 = Z_to_bv 64 sa -> a1 = Z_to_bv 64 n ->
  (0 <= sa)%Z -> (0 <= n)%Z -> (sa + n < 2^64)%Z ->
  rw_cells ctasegs m sa [CB (Z.to_nat n) junk] ->
  setshadow_cells m ->
  mem_inv ctasegs m ->
  evt ctasegs (memset_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sa v n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom ctasegs)).

Lemma set_shadow_00_spec : set_shadow_stmt 0x1c62cc 0.
Proof.
  unfold set_shadow_stmt. intros until junk. intros -> -> H0 Hn Hsn DST [GOT RM] MI.
  unfold g_got_real_memset, g_real_memset, musl_memset_entry in *.
  do 6 zstep.
  eapply memset_callZ with (junk := junk); [exact DST| exact MI| lia| lia| lia| lia].
Qed.

Lemma set_shadow_f5_spec : set_shadow_stmt 0x1c63d4 245.
Proof.
  unfold set_shadow_stmt. intros until junk. intros -> -> H0 Hn Hsn DST [GOT RM] MI.
  unfold g_got_real_memset, g_real_memset, musl_memset_entry in *.
  do 6 zstep.
  eapply memset_callZ with (junk := junk); [exact DST| exact MI| lia| lia| lia| lia].
Qed.

Lemma set_shadow_f8_spec : set_shadow_stmt 0x1c63ec 248.
Proof.
  unfold set_shadow_stmt. intros until junk. intros -> -> H0 Hn Hsn DST [GOT RM] MI.
  unfold g_got_real_memset, g_real_memset, musl_memset_entry in *.
  do 6 zstep.
  eapply memset_callZ with (junk := junk); [exact DST| exact MI| lia| lia| lia| lia].
Qed.
