(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_auto Sj_stage2_auto2
  Sj_stage2_numkit Sj_stage2_numo_defs Sj_stage2_numo_loops.
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
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.

Section NumO2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).

  Ltac n_exit KX := srun_to 0x444d0%Z; s2_err_exit KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
  Ltac n_scan KS pp := eapply (KS pp); [lia | eapply MEMI_OSL; [s2_close_mem0 | reflexivity ..]].

  Lemma seg_numo_fdig : forall (Q : machine_state -> Prop) (s : st) neg p d,
    (0 <= p)%Z -> (1 <= d)%Z -> (p + d <= e_len E)%Z -> exit_k E Q ->
    (forall p', (p < p' <= e_len E)%Z -> numo_scan_k E Q s neg (W s) 0x47838 p') ->
    numo_fdig_k E Q s neg (W s) p d.
  Proof using OK.
    intros Q s neg p d HP HD HPD KX KS. unfold numo_fdig_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs (p + d) BOK) as HB0.
    s2_env OK. unfold OFSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0; zify_cond K0.
    -
      srun.
      if_cases K1; zify_cond K1.
      + srun_to 0x47838%Z.
        replace (e_BUF E + p + d)%Z with (e_BUF E + (p + d))%Z by lia.
        n_scan KS (p + d)%Z.
      + n_exit KX.
    - assert (HNZ : (p + d < e_len E)%Z) by (apply B_nz_lt; lia).
      srun_to 0x47660%Z.
      replace (e_BUF E + p + d)%Z with (e_BUF E + (p + d))%Z by lia.
      eapply (numo_L3 E OK Q (S (Z.to_nat (e_len E)))); [exact BUFRO | lia | lia |].
      intros q' yt2 ya2 ya1 ya6 HQ'.
      srun_to 0x47838%Z.
      n_scan KS q'.
  Qed.

  Lemma seg_numo_ftail : forall (Q : machine_state -> Prop) (s : st) neg p d r,
    (0 <= p)%Z -> (1 <= d)%Z -> (r = p + d)%Z -> (r <= e_len E)%Z ->
    (forall d', (d <= d')%Z -> (p + d' <= e_len E)%Z -> numo_fdig_k E Q s neg (W s) p d') ->
    numo_ftail_k E Q s neg (W s) p d r.
  Proof using OK.
    intros Q s neg p d r HP HD HR HPD KD. unfold numo_ftail_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (B_range bs r BOK) as HB0. pose proof (B_range bs (r + 1) BOK) as HB1. pose proof (B_range bs (r + 2) BOK) as HB2.
    pose proof (B_range bs (r + 3) BOK) as HB3. pose proof (B_range bs (r + 4) BOK) as HB4. pose proof (B_range bs (r + 5) BOK) as HB5.
    pose proof (B_range bs (r + 6) BOK) as HB6. pose proof (B_range bs (r + 7) BOK) as HB7.
    s2_env OK. unfold OFSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0; zify_cond K0.
    - eapply (KD d); [lia | lia | unfold OFSL; s2_close_mem0].
    - pose proof (swar4_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 K0) as HL.
      assert (HNZ : (r + 3 < e_len E)%Z) by (apply B_nz_lt; lia).
      srun_to 0x47640%Z.
      eapply (KD (d + 4)%Z); [lia | lia | unfold OFSL; s2_close_mem0].
  Qed.

  Lemma seg_numo_frac : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (0 <= p < e_len E)%Z -> exit_k E Q ->
    (forall d r, (1 <= d)%Z -> (r = p + d)%Z -> (r <= e_len E)%Z -> numo_ftail_k E Q s neg (W s) p d r) ->
    numo_frac_k E Q s neg (W s) p.
  Proof using OK.
    intros Q s neg p HK HNEG HP KX KT. unfold numo_frac_k.
    intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (B_range bs (p + 1) BOK) as HB1. pose proof (B_range bs (p + 2) BOK) as HB2. pose proof (B_range bs (p + 3) BOK) as HB3.
    pose proof (B_range bs (p + 4) BOK) as HB4. pose proof (B_range bs (p + 5) BOK) as HB5. pose proof (B_range bs (p + 6) BOK) as HB6.
    pose proof (B_range bs (p + 7) BOK) as HB7. pose proof (B_range bs (p + 8) BOK) as HB8.
    s2_env OK. unfold OSL in HM.
    s2_open_mem HM.
    srun_to 0x474c4%Z. fold_V8.
    srun.
    if_cases K0; zify_cond K0.
    -
      replace (p + 2)%Z with (p + 1 + 1)%Z by lia. replace (p + 3)%Z with (p + 1 + 2)%Z by lia. replace (p + 4)%Z with (p + 1 + 3)%Z by lia.
      replace (p + 5)%Z with (p + 1 + 4)%Z by lia. replace (p + 6)%Z with (p + 1 + 5)%Z by lia. replace (p + 7)%Z with (p + 1 + 6)%Z by lia.
      replace (p + 8)%Z with (p + 1 + 7)%Z by lia.
      eapply (KT 1%Z (p + 1)%Z); [lia | lia | lia | unfold OFSL; s2_close_mem0].
    -
      pose proof (V8_range _ _ _ _ _ _ _ _ HB1 HB2 HB3 HB4 HB5 HB6 HB7 HB8) as HVR. rewrite ?(Z.mod_small _ _ HVR) in K0.
      pose proof (swar8_last _ _ _ _ _ _ _ _ HB1 HB2 HB3 HB4 HB5 HB6 HB7 HB8 K0) as HL.
      assert (HNZ : (p + 8 < e_len E)%Z) by (apply B_nz_lt; lia).
      srun_to 0x47530%Z.
      replace (e_BUF E + p + 9)%Z with (e_BUF E + (p + 9))%Z by lia.
      replace (Z_to_bv 64 1) with (Z_to_bv 64 (p + 9 - p - 8)) by (f_equal; lia).
      eapply (numo_L2 E OK Q (S (Z.to_nat (e_len E))) p (p + 9)%Z); [exact BUFRO | lia | lia |].
      intros q' ys3 yra ya1 yt1 ya6 yt0 ya2 ys5 HQ'.
      eapply (KT (q' - p)%Z q'); [lia | lia | lia | unfold OFSL; s2_close_mem0].
  Qed.
End NumO2.
