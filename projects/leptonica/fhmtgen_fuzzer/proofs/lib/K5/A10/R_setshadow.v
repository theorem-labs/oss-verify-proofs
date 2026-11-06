(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout F_memset.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition g_got_real_memset : Z := 0xe4028.   (* [comment removed for export] *)
Definition g_real_memset : Z := 0xe5ee0.       (* [comment removed for export] *)
Definition musl_memset_entry : Z := 0xda744.

(* [comment removed for export] *)
Definition setshadow_cells (m : mem) : Prop :=
  rw_cells asegs m g_got_real_memset [C8 (Z_to_bv 64 g_real_memset)]
  /\ rw_cells asegs m g_real_memset [C8 (Z_to_bv 64 musl_memset_entry)].

Definition set_shadow_stmt (entry v : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (sa n : Z) (junk : list byte),
  a0 = Z_to_bv 64 sa -> a1 = Z_to_bv 64 n ->
  (0 <= sa)%Z -> (0 <= n)%Z -> (sa + n < 2^64)%Z ->
  rw_cells asegs m sa [CB (Z.to_nat n) junk] ->
  setshadow_cells m ->
  mem_inv asegs m ->
  evt asegs (memset_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sa v n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma set_shadow_00_spec : set_shadow_stmt 0x648a0 0.
Proof.
  unfold set_shadow_stmt. intros until junk. intros -> -> H0 Hn Hsn DST [GOT RM] MI.
  unfold g_got_real_memset, g_real_memset, musl_memset_entry in *.
  do 6 zstep.
  eapply memset_callZ with (junk := junk); [exact DST| exact MI| lia| lia| lia| lia].
Qed.

Lemma set_shadow_f5_spec : set_shadow_stmt 0x649a8 245.
Proof.
  unfold set_shadow_stmt. intros until junk. intros -> -> H0 Hn Hsn DST [GOT RM] MI.
  unfold g_got_real_memset, g_real_memset, musl_memset_entry in *.
  do 6 zstep.
  eapply memset_callZ with (junk := junk); [exact DST| exact MI| lia| lia| lia| lia].
Qed.

Lemma set_shadow_f8_spec : set_shadow_stmt 0x649c0 248.
Proof.
  unfold set_shadow_stmt. intros until junk. intros -> -> H0 Hn Hsn DST [GOT RM] MI.
  unfold g_got_real_memset, g_real_memset, musl_memset_entry in *.
  do 6 zstep.
  eapply memset_callZ with (junk := junk); [exact DST| exact MI| lia| lia| lia| lia].
Qed.
