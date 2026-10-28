(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2
  Sj_stage2_numa_defs Sj_stage2_numa_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section NumA1.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).
  Notation o s := (e_off E (k s)).

  Lemma seg_numa_entry : forall (Q : machine_state -> Prop) (s : st),
    (0 <= k s <= e_n E)%Z -> exit_k E Q ->
    (forall neg p, is_numstart (e_tok E (k s)) = true ->
       (0 <= neg <= 1)%Z -> (o s + neg < LEN)%Z -> (o s + neg < p <= LEN)%Z -> numa_dot_k E Q s neg p) ->
    arrnum_k E Q s.
  Proof using OK SHZ.
    intros Q s HK KX KD. unfold arrnum_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    s2_env OK.
    nopen HM.
    ngrun_to 0xc66c4%Z.
    match goal with |- context [Z.b2z ?c] =>
      assert (HNEG : (0 <= Z.b2z c <= 1)%Z) by (destruct c; cbn; lia);
      assert (HNS : Z.b2z c = 0%Z \/ e_tok E (k s) = 45%Z)
        by (destruct c eqn:EC; [right; apply Z.ltb_lt in EC; lia | left; reflexivity]);
      set (neg := Z.b2z c) in *; clearbody neg end.
    pose proof (B_range bs (o s + neg) BOK) as HB0.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun. if_cases K1; zify_cond K1; try (exfalso; lia).
      nexit KX.
    -
      assert (HS : (o s + neg < LEN)%Z) by (nz_lt_by ltac:(lia)).
      assert (HNUM : is_numstart (e_tok E (k s)) = true).
      { unfold is_numstart, is_digit, c_minus. destruct HNS as [N0 | N45].
        - subst neg. replace (o s + 0)%Z with (o s) in K0 by lia. unfold tok in *.
          apply orb_true_iff. right. apply andb_true_iff. split; apply Z.leb_le; lia.
        - rewrite N45. reflexivity. }
      ngrun_to 0xc6710%Z.
      kapply (numa_L1 E OK SHZ Q (S (Z.to_nat (LEN))) (o s + neg)%Z); [nclose | lia | lia |].
      intros p'. intro_words. intros HP'.
      pose proof (B_range bs p' BOK) as HBP.
      ngrun.
      if_cases K2; zify_cond K2; try (exfalso; lia).
      ngrun.
      if_cases K3; zify_cond K3.
      + kapply (KD neg p' HNUM HNEG HS ltac:(lia)). nclose.
      + ngrun.
        if_cases K4; zify_cond K4;
          first [ (kapply (KD neg p' HNUM HNEG HS ltac:(lia)); nclose) | nexit KX ].
  Qed.
End NumA1.
