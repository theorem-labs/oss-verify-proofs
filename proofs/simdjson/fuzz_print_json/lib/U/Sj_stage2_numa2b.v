(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numa_defs Sj_stage2_numa_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_store_done_wr_v2.

Section NumA2b.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).

  Ltac n_exit KX := ngrun_to 0x4be14%Z; eapply KX; [s2_errok_code | s2_close_memx].
  Ltac n_close := unfold NSL; s2_close_mem0.

  Lemma seg_numa_frac : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (0 <= p < e_len E)%Z ->
    (forall d r, (1 <= d)%Z -> (r = p + d)%Z -> (r <= e_len E)%Z -> numa_ftail_k E Q s neg p d r) ->
    numa_frac_k E Q s neg p.
  Proof using OK.
    intros Q s neg p HK HNEG HP KT. unfold numa_frac_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (B_range bs (p + 1) BOK) as HB1. pose proof (B_range bs (p + 2) BOK) as HB2. pose proof (B_range bs (p + 3) BOK) as HB3.
    pose proof (B_range bs (p + 4) BOK) as HB4. pose proof (B_range bs (p + 5) BOK) as HB5. pose proof (B_range bs (p + 6) BOK) as HB6.
    pose proof (B_range bs (p + 7) BOK) as HB7. pose proof (B_range bs (p + 8) BOK) as HB8.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    ngrun_to 0x4808c%Z. fold_V8.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      replace (p + 2)%Z with (p + 1 + 1)%Z by lia. replace (p + 3)%Z with (p + 1 + 2)%Z by lia. replace (p + 4)%Z with (p + 1 + 3)%Z by lia.
      replace (p + 5)%Z with (p + 1 + 4)%Z by lia. replace (p + 6)%Z with (p + 1 + 5)%Z by lia. replace (p + 7)%Z with (p + 1 + 6)%Z by lia.
      replace (p + 8)%Z with (p + 1 + 7)%Z by lia.
      eapply (KT 1%Z (p + 1)%Z); [lia | lia | lia | n_close].
    -
      pose proof (V8_range _ _ _ _ _ _ _ _ HB1 HB2 HB3 HB4 HB5 HB6 HB7 HB8) as HVR. rewrite ?(Z.mod_small _ _ HVR) in K0.
      pose proof (swar8_last _ _ _ _ _ _ _ _ HB1 HB2 HB3 HB4 HB5 HB6 HB7 HB8 K0) as HL.
      assert (HNZ : (p + 8 < e_len E)%Z) by (apply B_nz_lt; lia).
      ngrun_to 0x480f8%Z.
      replace (e_BUF E + p + 9)%Z with (e_BUF E + (p + 9))%Z by lia.
      replace (Z_to_bv 64 1) with (Z_to_bv 64 (p + 9 - p - 8)) by (f_equal; lia).
      eapply (numa_L2 E OK Q (S (Z.to_nat (e_len E))) p (p + 9)%Z); [exact BUFRO | lia | lia |].
      intros q' ys7 ys8 ys9 ys10 ys11 yra ya3 yt5 HQ'.
      eapply (KT (q' - p)%Z q'); [lia | lia | lia | n_close].
  Qed.
End NumA2b.
