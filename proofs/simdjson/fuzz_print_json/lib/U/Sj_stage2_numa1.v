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

Section NumA1.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).

  Ltac n_exit KX := ngrun_to 0x4be14%Z; eapply KX; [s2_errok_code | s2_close_memx].

  Lemma seg_numa_entry : forall (Q : machine_state -> Prop) (s : st),
    (0 <= k s <= e_n E)%Z -> exit_k E Q ->
    (forall neg p, is_numstart (e_tok E (k s)) = true ->
       (0 <= neg <= 1)%Z -> (o s + neg < e_len E)%Z -> (o s + neg < p <= e_len E)%Z -> B bs p = 46%Z -> numa_frac_k E Q s neg p) ->
    (forall neg p, is_numstart (e_tok E (k s)) = true ->
       (0 <= neg <= 1)%Z -> (o s + neg < e_len E)%Z -> (o s + neg < p <= e_len E)%Z -> numa_scan_k E Q s neg p 0 (B bs p)) ->
    arrnum_k E Q s.
  Proof using OK.
    intros Q s HK KX KF KS. unfold arrnum_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    s2_env OK.
    s2_open_mem HM.
    ngrun_to 0x47f50%Z.
    match goal with |- context [Z.b2z ?c] =>
      assert (HNEG : (0 <= Z.b2z c <= 1)%Z) by (destruct c; cbn; lia);
      assert (HNS : Z.b2z c = 0%Z \/ e_tok E (k s) = 45%Z)
        by (destruct c eqn:EC; [right; apply Z.ltb_lt in EC; lia | left; reflexivity]);
      set (neg := Z.b2z c) in *; clearbody neg end.
    pose proof (B_range bs (o s + neg) BOK) as HB0.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun. if_cases K1; zify_cond K1; [exfalso; lia|].
      n_exit KX.
    -
      assert (HS : (o s + neg < e_len E)%Z) by (apply B_nz_lt; lia).
      assert (HNUM : is_numstart (e_tok E (k s)) = true).
      { unfold is_numstart, is_digit, c_minus. destruct HNS as [N0 | N45].
        - subst neg. replace (o s + 0)%Z with (o s) in K0 by lia. unfold tok in *.
          apply orb_true_iff. right. apply andb_true_iff. split; apply Z.leb_le; lia.
        - rewrite N45. reflexivity. }
      ngrun_to 0x47f94%Z.
      replace (e_BUF E + o s + neg)%Z with (e_BUF E + (o s + neg))%Z by lia.
      replace (e_BUF E + neg + o s)%Z with (e_BUF E + (o s + neg))%Z by lia.
      eapply (numa_L1 E OK Q (S (Z.to_nat (e_len E)))); [exact BUFRO | lia | lia |].
      intros p' ya3 yt4 ya0 yt5 HP'.
      pose proof (B_range bs p' BOK) as HBP.
      ngrun.
      if_cases K2; zify_cond K2.
      2:{ n_exit KX. }
      ngrun.
      if_cases K3; zify_cond K3.
      + ngrun.
        if_cases K5; zify_cond K5.
        * ngrun_to 0x484dc%Z. eapply (KS neg p' HNUM HNEG HS ltac:(lia)). unfold NSL. s2_close_mem0.
        * ngrun_to 0x47ff4%Z. eapply (KF neg p' HNUM HNEG HS ltac:(lia) ltac:(lia)). unfold NSL. s2_close_mem0.
      + ngrun.
        if_cases K4; zify_cond K4.
        2:{ n_exit KX. }
        ngrun.
        if_cases K5; zify_cond K5.
        * ngrun_to 0x484dc%Z. eapply (KS neg p' HNUM HNEG HS ltac:(lia)). unfold NSL. s2_close_mem0.
        * ngrun_to 0x47ff4%Z. eapply (KF neg p' HNUM HNEG HS ltac:(lia) ltac:(lia)). unfold NSL. s2_close_mem0.
  Qed.
End NumA1.
