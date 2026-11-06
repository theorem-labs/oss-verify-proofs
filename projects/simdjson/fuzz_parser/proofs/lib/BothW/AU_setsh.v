(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase RtCells ShadowTac F_memset.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition ASETSH_F5 : Z := 0x694c4.
Definition ASETSH_00 : Z := 0x693bc.

(* [comment removed for export] *)
Definition setsh_cells (m : amem) : Prop :=
  rw_cells bsegs m 0x112aa0 [C8 (Z_to_bv 64 0x1149c8)] /\ rt_real_mem m.

Definition setsh_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (v : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) (repeat (Z_to_bv 8 v) (Z.to_nat (bv_unsigned a1)))].

Definition set_shadow_stmt (entry v : Z) : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (junk : list byte),
  mem_inv bsegs m -> setsh_cells m ->
  rw_cells bsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) junk] ->
  rng RNG (bv_unsigned a0) (bv_unsigned a1) -> rng_aimg RNG ->
  evtF bsegs RNG (setsh_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc a0 a1 v m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

Lemma memset_to_setsh : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (a0 a1 : word) (v : Z) m ms',
  0 <= v < 256 ->
  memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc a0 (Z_to_bv 64 v) a1 m ms' ->
  setsh_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc a0 a1 v m ms'.
Proof.
  intros until ms'. intros Hv (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI & RW).
  exists t0, t1, t2, a1', a2', a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  rewrite unsigned_lit in RW by lia. rewrite Z.mod_small in RW by lia. exact RW.
Qed.

Theorem set_shadow_f5_spec : set_shadow_stmt ASETSH_F5 245.
Proof.
  unfold set_shadow_stmt. intros until junk. intros MI (GOT & REAL) DST RD RIMG.
  unfold ASETSH_F5.
  zstep. zstep. zstep. zstep. zstep. zstep.
  eapply evtF_mono; [eapply memset_spec; [exact DST | exact MI | exact RD] |].
  intros ms' PO. apply memset_to_setsh; [lia| exact PO].
Qed.

Theorem set_shadow_00_spec : set_shadow_stmt ASETSH_00 0.
Proof.
  unfold set_shadow_stmt. intros until junk. intros MI (GOT & REAL) DST RD RIMG.
  unfold ASETSH_00.
  zstep. zstep. zstep. zstep. zstep. zstep.
  eapply evtF_mono; [eapply memset_spec; [exact DST | exact MI | exact RD] |].
  intros ms' PO. apply memset_to_setsh; [lia| exact PO].
Qed.
End CANSEC1.
