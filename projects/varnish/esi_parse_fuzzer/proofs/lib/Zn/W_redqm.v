(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image ZBridge Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition realloc_sym : Z := 0x24bd0.
Definition malloc_sym : Z := 0x23364.
Definition free_sym : Z := 0x23224.
Definition malloc_impl_entry : Z := 0x23cf4.
Definition free_impl_entry : Z := 0x23368.

Lemma realloc_null_evt : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 malloc_impl_entry) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 realloc_sym) fc None m (seg_rom rsegs)).
Proof.
  intros. unfold realloc_sym, malloc_impl_entry.
  step. step. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity].
  step. step. apply evt_done. reflexivity.
Qed.

Lemma malloc_sym_evt : forall R F fc m,
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 malloc_impl_entry) fc None m (seg_rom rsegs))
      (MS R F (Z_to_bv 64 malloc_sym) fc None m (seg_rom rsegs)).
Proof. intros. unfold malloc_sym, malloc_impl_entry. step. apply evt_done. reflexivity. Qed.

Lemma free_sym_evt : forall R F fc m,
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 free_impl_entry) fc None m (seg_rom rsegs))
      (MS R F (Z_to_bv 64 free_sym) fc None m (seg_rom rsegs)).
Proof. intros. unfold free_sym, free_impl_entry. step. apply evt_done. reflexivity. Qed.
