(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_auto Sj_stage2_auto2 Sj_stage2_objf
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

Section NumO1.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).

  Lemma seg_numo_entry : forall (Q : machine_state -> Prop) (s : st),
    (0 <= k s <= e_n E)%Z -> exit_k E Q ->
    (forall neg p, is_numstart (e_tok E (k s)) = true ->
       (0 <= neg <= 1)%Z -> (o s + neg < e_len E)%Z -> (o s + neg < p <= e_len E)%Z -> B bs p = 46%Z -> numo_frac_k E Q s neg (W s) p) ->
    (forall neg p, is_numstart (e_tok E (k s)) = true ->
       (0 <= neg <= 1)%Z -> (o s + neg < e_len E)%Z -> (o s + neg < p <= e_len E)%Z -> numo_scan_k E Q s neg (W s) 0x4a260 p) ->
    objval_k E Q 0x49dbc s.
  Proof using OK.
    intros Q s HK KX KF KS. unfold objval_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK.
    pose proof (off_bound E OK (k s) HK) as HO. pose proof (tok_range E OK (k s)) as HT.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    s2_env OK.
    s2_open_mem HM.
    srun_to 0x49dd4%Z.
    match goal with |- context [Z.b2z ?c] =>
      assert (HNEG : (0 <= Z.b2z c <= 1)%Z) by (destruct c; cbn; lia);
      assert (HNS : Z.b2z c = 0%Z \/ e_tok E (k s) = 45%Z)
        by (destruct c eqn:EC; [right; apply Z.ltb_lt in EC; lia | left; reflexivity]);
      set (neg := Z.b2z c) in *; clearbody neg end.
    pose proof (B_range bs (o s + neg) BOK) as HB0.
    srun.
    if_cases K0; zify_cond K0.
    -
      srun. if_cases K1; zify_cond K1; try (exfalso; lia).
      srun_to 0x46ef8%Z. s2_err_exit KX.
      eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
    -
      assert (HS : (o s + neg < e_len E)%Z) by (apply B_nz_lt; lia).
      assert (HNUM : is_numstart (e_tok E (k s)) = true).
      { unfold is_numstart, is_digit, c_minus. destruct HNS as [N0 | N45].
        - subst neg. replace (o s + 0)%Z with (o s) in K0 by lia. unfold tok in *.
          apply orb_true_iff. right. apply andb_true_iff. split; apply Z.leb_le; lia.
        - rewrite N45. reflexivity. }
      srun_to 0x49dfc%Z.
      replace (e_BUF E + o s + neg)%Z with (e_BUF E + (o s + neg))%Z by lia.
      eapply (numo_L1 E OK Q (S (Z.to_nat (e_len E)))); [exact BUFRO | lia | lia |].
      intros p' ya2 yt1 yt4 yt5 HP'.
      pose proof (B_range bs p' BOK) as HBP.
      assert (REST : forall yt1' yt2',
        evt psegs Q (S2R E 0x49e40 xra (Z_to_bv 64 (e_tok E (k s) + -45)) yt1' yt2' (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 (e_tok E (k s)))
                         (Z_to_bv 64 (e_BUF E + (o s + neg))) ya2 (Z_to_bv 64 (o s)) (Z_to_bv 64 (B bs (o s + neg))) (Z_to_bv 64 (e_BUF E + p'))
                         (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) (Z_to_bv 64 (B bs p')) (Z_to_bv 64 (e_BUF E + o s)) xs3 (Z_to_bv 64 (e_BUF E))
                         xs5 xs6 xs7 (Z_to_bv 64 (e_SBUF E + sb s + -1)) xs9 xs10 (Z_to_bv 64 (e_SBUF E + sb s))
                         (Z_to_bv 64 (e_BUF E + p')) yt4 yt5 xt6 F fc m0)).
      { intros yt1' yt2'. srun.
        if_cases K5; zify_cond K5.
        - srun_to 0x4a260%Z. eapply (KS neg p' HNUM HNEG HS ltac:(lia)). unfold OSL. s2_close_mem0.
        - eapply (KF neg p' HNUM HNEG HS ltac:(lia) ltac:(lia)). unfold OSL. s2_close_mem0. }
      srun.
      if_cases K2; zify_cond K2.
      + srun. if_cases K3; zify_cond K3.
        * apply REST.
        * srun. if_cases K4; zify_cond K4.
          -- apply REST.
          -- srun_to 0x46ef8%Z. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
      + srun_to 0x46ef8%Z. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
  Qed.
End NumO1.
