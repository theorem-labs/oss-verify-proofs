(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import F_memset.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition memset_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (dst c len : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(dst, dst + len)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' dst [CB (Z.to_nat len) (repeat (Z_to_bv 8 c) (Z.to_nat len))].

Lemma memset_specZ : forall RNG (dst c len : Z) (junk : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 len ->
  0 <= dst -> 0 <= len -> dst + len < 2^64 -> 0 <= c < 256 ->
  rw_cells bsegs m dst [CB (Z.to_nat len) junk] ->
  mem_inv bsegs m ->
  rng RNG dst len ->
  evtF bsegs RNG (memset_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst c len m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xc0a3c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros -> -> -> D0 L0 DL C DST MI RR.
  eapply evtF_mono.
  - eapply memset_spec; [| exact MI |]; rewrite !unsigned_lit by lia; [exact DST | exact RR].
  - intros ms' PO. unfold memset_post in PO. unfold memset_postZ. destruct_exs PO.
    destruct PO as (-> & MU & WM & MI2 & DST2).
    rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit in DST2 by lia. rewrite (Z.mod_small c 256) in DST2 by lia.
    do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. exact DST2.
Qed.
End CANSEC1.
