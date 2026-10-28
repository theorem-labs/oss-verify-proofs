(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Printf_lib.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ImageA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation bsegs := ImageA.bsegs.

Notation USELOC_ENTRY := 0x1628d8%Z (only parsing).
Notation LOC_CELL := 0x6be3b8%Z (only parsing).
Notation GLOC := 0x6de6b0%Z (only parsing).

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

Definition usel_new (old loc : Z) : Z := if loc =? 0 then old else if loc =? 2^64 - 1 then GLOC else loc.
Definition usel_ret (old : Z) : Z := if old =? GLOC then 2^64 - 1 else old.

Lemma lor_ones64 : forall x, 0 <= x < 2^64 -> Z.lor 18446744073709551615 x = 18446744073709551615.
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  change 18446744073709551615 with (Z.ones 64).
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. cbn.
    destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia].
Qed.
Lemma usel_ret_eq : forall old, 0 <= old < 2^64 ->
  Z.lor (Z.land (Z.b2z (0 <? Z.lxor old 7202480) + -1) 18446744073709551615) old = usel_ret old.
Proof.
  intros old Hold. unfold usel_ret.
  destruct (Z.eqb_spec old 7202480) as [->|NE].
  - rewrite Z.lxor_nilpotent. cbn. apply lor_ones64. lia.
  - assert (NZ : Z.lxor old 7202480 <> 0) by (intros E; apply Z.lxor_eq in E; lia).
    pose proof (Z.lxor_nonneg old 7202480) as NN.
    replace (0 <? Z.lxor old 7202480) with true by (symmetry; apply Z.ltb_lt; lia). cbn. reflexivity.
Qed.

Definition uselocale_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (old loc : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (usel_ret old)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(LOC_CELL, LOC_CELL + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' LOC_CELL [C8 (Z_to_bv 64 (usel_new old loc))].

Lemma uselocale_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (old loc : Z),
  tp = Z_to_bv 64 (LOC_CELL + 48) -> a0 = Z_to_bv 64 loc -> (0 <= loc < 2^64) -> (0 <= old < 2^64) ->
  rw_cells bsegs m LOC_CELL [C8 (Z_to_bv 64 old)] -> mem_inv bsegs m ->
  evt bsegs (uselocale_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old loc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 USELOC_ENTRY) fc None m (seg_rom bsegs)).
Proof.
  intros until loc. intros -> -> Hloc Hold CELL MI.
  pose proof (munch_refl [(0x6be3b8, 0x6be3b8 + 8)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zs. zs. zs. zs.
  zs. if_cases K0; zify_cond K0.
  -
    zs. zs. zs. zs. zs. zs.
    rewrite (usel_ret_eq old Hold).
    apply evt_done. unfold uselocale_post, usel_new. try rewrite !unsigned_lit in K0 by lia.
    replace (loc =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact CELL.
  - try rewrite !unsigned_lit in K0 by lia.
    zs. zs. if_cases K1; zify_cond K1; try rewrite !unsigned_lit in K1 by lia.
    +
      zs.
      zs. zs. zs. zs. zs. zs.
      rewrite (usel_ret_eq old Hold).
      apply evt_done. unfold uselocale_post, usel_new.
      replace (loc =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (loc =? 2^64 - 1) with false by (symmetry; apply Z.eqb_neq; lia).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      match goal with H : rw_cells _ _ 7070648 _ |- _ => exact H end.
    +
      zs. zs.
      zs. zs. zs. zs. zs. zs.
      rewrite (usel_ret_eq old Hold).
      apply evt_done. unfold uselocale_post, usel_new.
      replace (loc =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (loc =? 2^64 - 1) with true by (symmetry; apply Z.eqb_eq; lia).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      match goal with H : rw_cells _ _ 7070648 _ |- _ => exact H end.
Qed.

