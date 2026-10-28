(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numo_defs Sj_stage2_numo_loops.
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

Section NumO2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).

  Ltac n_exit KX := ngrun_to 0x4bfd0%Z; eapply KX; [s2_errok_code | s2_close_memx].
  Ltac n_close := first [unfold NSL; s2_close_mem0 | eapply MEMI_NSL; [s2_close_mem0 | reflexivity ..]].

  Lemma seg_numo_fdig : forall (Q : machine_state -> Prop) (s : st) neg p d x,
    (0 <= p)%Z -> (1 <= d)%Z -> (p + d <= e_len E)%Z -> (0 <= x < 2^64)%Z -> (x mod 256 = B bs (p + d))%Z -> exit_k E Q ->
    (forall d' x', (d <= d')%Z -> (p + d' <= e_len E)%Z -> (0 <= x' < 2^64)%Z -> (x' mod 256 = B bs (p + d'))%Z ->
       numo_scan_k E Q s neg (p + d') (1 - d') x') ->
    numo_fdig_k E Q s neg p d x.
  Proof using OK.
    intros Q s neg p d x HP HD HPD HX HXB KX KS. unfold numo_fdig_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs (p + d) BOK) as HB0.
    pose proof (low_sub48 x _ HXB) as HX48.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun.
      if_cases K1; zify_cond K1.
      + n_exit KX.
      + ngrun_to 0x4b764%Z.
        replace (e_BUF E + p + d)%Z with (e_BUF E + (p + d))%Z by lia.
        eapply (KS d x); [lia | lia | lia | exact HXB | n_close].
    - assert (HNZ : (p + d < e_len E)%Z) by (apply B_nz_lt; lia).
      ngrun_to 0x4b504%Z.
      eapply (numo_L3 E OK Q (S (Z.to_nat (e_len E))) p d); [exact BUFRO | lia | lia | lia | lia |].
      intros d' ya2 ya3 yt2 ya6 HD' HPD'.
      pose proof (B_range bs (p + d') BOK) as HBD.
      ngrun_to 0x4b764%Z.
      replace (e_BUF E + p + d')%Z with (e_BUF E + (p + d'))%Z by lia.
      eapply (KS d' (B bs (p + d'))); [lia | lia | lia | apply Z.mod_small; lia | n_close].
  Qed.

  Lemma seg_numo_ftail : forall (Q : machine_state -> Prop) (s : st) neg p d r,
    (0 <= p)%Z -> (1 <= d)%Z -> (r = p + d)%Z -> (r <= e_len E)%Z ->
    (forall d' x, (d <= d')%Z -> (p + d' <= e_len E)%Z -> (0 <= x < 2^64)%Z -> (x mod 256 = B bs (p + d'))%Z -> numo_fdig_k E Q s neg p d' x) ->
    numo_ftail_k E Q s neg p d r.
  Proof using OK.
    intros Q s neg p d r HP HD HR HPD KD. unfold numo_ftail_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (B_range bs r BOK) as HB0. pose proof (B_range bs (r + 1) BOK) as HB1. pose proof (B_range bs (r + 2) BOK) as HB2.
    pose proof (B_range bs (r + 3) BOK) as HB3. pose proof (B_range bs (r + 4) BOK) as HB4. pose proof (B_range bs (r + 5) BOK) as HB5.
    pose proof (B_range bs (r + 6) BOK) as HB6. pose proof (B_range bs (r + 7) BOK) as HB7.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0; zify_cond K0.
    - pose proof (V8_range _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVR.
      pose proof (V8_low _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVL.
      eapply (KD d); [lia | lia | exact HVR | rewrite HVL; f_equal; lia | n_close].
    - pose proof (swar4_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 K0) as HL.
      assert (HNZ : (r + 3 < e_len E)%Z) by (apply B_nz_lt; lia).
      pose proof (B_range bs (p + (d + 4)) BOK) as HB4'.

      ngrun_cut_f ltac:(fun pc => lazymatch pc with 0x4b4e8%Z => fail | _ => idtac end)
                  ltac:(fun n => lazymatch n with 6%Z => fail | 12%Z => fail | 14%Z => fail | 15%Z => fail | 17%Z => fail | 9%Z => fail | 21%Z => fail | 25%Z => fail | _ => idtac end).
      eapply (KD (d + 4)%Z (B bs (p + (d + 4)))); [lia | lia | lia | apply Z.mod_small; lia | n_close].
  Qed.

End NumO2.
